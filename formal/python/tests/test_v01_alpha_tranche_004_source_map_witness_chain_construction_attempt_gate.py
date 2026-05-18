from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_report import (
    BLOCKER_REASON,
    CONSTRUCTION_ATTEMPT_CLASSIFICATION,
    CURRENT_BLOCKER,
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
    ATTEMPT_ID,
    build_attempt,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
ATTEMPT_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01Tranche004SourceMapWitnessChainConstructionAttempt.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
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


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert ATTEMPT_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_consumes_result_review() -> None:
    attempt = _json(ATTEMPT_PATH)
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert attempt["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert attempt["accepted"] is True
    assert attempt["outcome_id"] == OUTCOME_ID
    assert attempt["consumes_construction_packet_result_review"] == (
        "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_RESULT_REVIEW_v0"
    )
    assert attempt["consumes_construction_packet_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_scope() -> None:
    attempt = _json(ATTEMPT_PATH)
    assert attempt["attempt_scope"] == (
        "EXECUTE_BOUNDED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_"
        "ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_RELEASE_PROMOTION_OR_READINESS_MARKING"
    )
    assert attempt["tranche_001_status"] == TRANCHE_001_STATUS
    assert attempt["tranche_002_status"] == TRANCHE_002_STATUS
    assert attempt["tranche_003_status"] == TRANCHE_003_STATUS
    assert attempt["tranche_004_status"] == (
        "construction_attempt_failed_retained_blocker_pending_result_review"
    )
    assert attempt["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert attempt["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert attempt["selected_dependency"] == SELECTED_DEPENDENCY
    assert attempt["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_preserves_blocker_and_lean_posture() -> None:
    attempt = _json(ATTEMPT_PATH)
    assert attempt["current_blocker"] == CURRENT_BLOCKER
    assert attempt["blocker_reason"] == BLOCKER_REASON
    assert attempt["source_map_authorization_status"]["authorization_status"] == CURRENT_BLOCKER
    assert attempt["source_map_authorization_status"]["full_source_map_semantic_closure_authorized"] is False
    assert attempt["source_map_authorization_status"]["not_authorized_reason"] == BLOCKER_REASON
    assert attempt["lean_audit_result"]["parsed_axioms"] == LEAN_AXIOMS_USED
    assert attempt["lean_audit_result"]["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert attempt["lean_audit_result"]["project_axiom_count"] == 0
    assert attempt["lean_audit_result"]["depends_on_no_axioms"] is True
    assert attempt["project_axioms_used"] == PROJECT_AXIOMS_USED


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_executes_bounded_attempt_only() -> None:
    attempt = _json(ATTEMPT_PATH)
    assert attempt["source_map_witness_chain_construction_attempt_executed"] is True
    assert attempt["source_map_witness_chain_construction_attempt_authorized_by_prior_review"] is True
    assert attempt["construction_attempt_classification"] == CONSTRUCTION_ATTEMPT_CLASSIFICATION
    assert len(attempt["attempt_execution_steps"]) == 5
    assert [step["step_id"] for step in attempt["attempt_execution_steps"]] == [
        "attempt_001_bind_negative_readout_to_attempt",
        "attempt_002_check_required_component_witnesses",
        "attempt_003_check_semantic_closure_conditions",
        "attempt_004_preserve_clean_lean_audit_surface",
        "attempt_005_fail_closed_pending_result_review",
    ]
    assert attempt["attempt_result"]["classification"] == CONSTRUCTION_ATTEMPT_CLASSIFICATION
    assert attempt["attempt_result"]["retained_blocker"] is True
    assert attempt["attempt_result"]["requires_result_review_before_any_status_adjudication"] is True


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_fails_closed_without_witnesses() -> None:
    attempt = _json(ATTEMPT_PATH)
    assert attempt["required_witness_chain_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
    assert attempt["constructed_witness_components"] == []
    assert attempt["missing_witness_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
    assert attempt["missing_witness_count"] == 10
    assert attempt["witness_chain_constructed"] is False
    assert attempt["partial_witness_chain_constructed"] is False
    assert attempt["source_map_witness_chain_evidence_constructed"] is False
    assert attempt["source_map_witness_chain_construction_successful"] is False
    assert attempt["attempt_result"]["constructed_witness_components"] == []
    assert attempt["attempt_result"]["missing_witness_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
    assert attempt["attempt_result"]["missing_witness_count"] == 10


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_does_not_claim_source_map_closure() -> None:
    attempt = _json(ATTEMPT_PATH)
    assert attempt["required_source_map_semantic_closure_conditions"] == (
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
    )
    assert attempt["satisfied_source_map_semantic_closure_conditions"] == []
    assert attempt["unsatisfied_source_map_semantic_closure_conditions"] == (
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
    )
    assert attempt["unsatisfied_source_map_semantic_closure_condition_count"] == 5
    assert attempt["source_map_closure_claimed"] is False
    assert attempt["source_map_semantic_closure_authorized"] is False
    assert attempt["qft_gr_seam_closed"] is False
    assert attempt["retained_blocker"] is True
    assert attempt["retained_blocker_reason"] == BLOCKER_REASON
    assert attempt["remains_release_blocking"] is True


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_keeps_blockers_tracked() -> None:
    attempt = _json(ATTEMPT_PATH)
    rows = attempt["release_blocking_obligations_carry_forward"]
    assert attempt["release_blocking_obligation_count"] == 3
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS
    selected = attempt["selected_release_blocking_obligation"]
    assert selected["dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY
    assert selected["dependency_class"] == SELECTED_DEPENDENCY_CLASS
    for row in rows:
        assert row["modified_by_tranche_003"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_003"


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_no_release_movement_or_debt_discharge() -> None:
    attempt = _json(ATTEMPT_PATH)
    assert attempt["source_map_authorization_status_adjudication_packet_preparation_authorized"] is False
    assert attempt["retained_source_map_blocker_declaration_preparation_authorized"] is False
    assert attempt["documentation_alone_can_clear_blocker"] is False
    assert attempt["blocker_movement_authorized"] is False
    assert attempt["blocker_movement_registered"] is False
    assert attempt["blocker_fully_remediated"] is False
    assert attempt["release_packet_assembled"] is False
    assert attempt["v01_alpha_marked_ready"] is False
    assert attempt["lean_theorem_debt_discharged"] is False
    assert attempt["axiom_spec_backed_debt_reduced"] is False
    assert attempt["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert attempt["proof_debt_reduced"] is False
    assert attempt["retained_assumptions_discharged"] is False
    assert attempt["validation_claim_authorized"] is False


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_forbidden_effects_false() -> None:
    attempt = _json(ATTEMPT_PATH)
    forbidden = attempt["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_next_target() -> None:
    attempt = _json(ATTEMPT_PATH)
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["selected_next_target_kind"] == (
        "tranche_004_source_map_witness_chain_construction_attempt_result_review_only"
    )
    assert attempt["selection_count"] == 1
    assert attempt["next_action_scope"] == (
        "REVIEW_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_"
        "ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_RELEASE_PROMOTION_OR_READINESS_MARKING"
    )
    assert {row["target"]: row["decision"] for row in attempt["candidate_next_targets"]} == {
        "review_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_result": "selected",
        "prepare_source_map_authorization_status_adjudication_packet": "deferred",
        "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration": "deferred",
    }


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_acceptance_and_determinism() -> None:
    attempt = _json(ATTEMPT_PATH)
    for key, value in attempt["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_attempt(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_attempt(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert attempt == generated_1


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        ATTEMPT_ID,
        "formal/docs/release/V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_20260515_v0.json",
        "formal/python/tools/v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_report.py",
        "formal/python/tests/test_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_gate.py",
        OUTCOME_ID,
        CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_ATTEMPT_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01Tranche004SourceMapWitnessChainConstructionAttempt" in index_text
    assert (
        "v01_tranche_004_source_map_witness_chain_construction_attempt_fails_closed"
        in index_text
    )
