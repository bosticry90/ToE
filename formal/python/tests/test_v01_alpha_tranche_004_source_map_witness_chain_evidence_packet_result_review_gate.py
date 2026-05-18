from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_report import (
    BLOCKER_REASON,
    CURRENT_BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AXIOMS_USED,
    NEXT_TARGET,
    OUTCOME_ID,
    PROJECT_AXIOMS_USED,
    REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
    REQUIRED_WITNESS_CHAIN_COMPONENTS,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
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
PACKET_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01Tranche004SourceMapWitnessChainEvidencePacketResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "source_map_closure_claimed",
    "source_map_semantic_closure_authorized",
    "witness_chain_constructed",
    "source_map_witness_chain_evidence_constructed",
    "source_map_witness_chain_evidence_construction_authorized",
    "evidence_construction_executed",
    "bounded_witness_chain_construction_executed",
    "remediation_execution_authorized",
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


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_consumes_packet() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_witness_chain_evidence_packet"] == (
        "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_v0"
    )
    assert review["consumes_witness_chain_evidence_packet_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_20260515_v0.json"
    )


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_scope() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "REVIEW_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_ONLY_"
        "NO_SOURCE_MAP_CLOSURE_WITNESS_CONSTRUCTION_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == TRANCHE_003_STATUS
    assert review["tranche_004_status"] == (
        "requirements_only_accepted_source_map_closure_still_unauthorized_pending_"
        "construction_packet_preparation"
    )
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert review["selected_dependency"] == SELECTED_DEPENDENCY
    assert review["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_preserves_blocker_and_lean_posture() -> None:
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


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_accepts_requirements_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["requirements_only_accepted"] is True
    assert review["evidence_requirements_scope"]["scope_kind"] == (
        "SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_REQUIREMENTS_PREPARATION_ONLY"
    )
    assert len(review["known_available_evidence"]) >= 4
    assert len(review["known_missing_evidence"]) >= 5
    assert review["required_witness_chain_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
    assert review["required_source_map_semantic_closure_conditions"] == (
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
    )
    assert review["documentation_alone_can_clear_blocker"] is False
    assert review["remains_release_blocking"] is True


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_selects_construction_packet_preparation_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["route_decision"]["selected_branch"] == (
        "bounded_source_map_witness_chain_construction_packet_preparation"
    )
    assert review["route_decision"]["selected_target"] == NEXT_TARGET
    assert review["route_decision"]["retained_blocker_declaration_branch"] == "deferred"
    assert review["route_decision"]["source_map_evidence_gap_refinement_packet_branch"] == (
        "deferred"
    )
    basis = review["construction_packet_preparation_basis"]
    assert basis["requirements_complete_enough_for_packet_preparation"] is True
    assert basis["construction_packet_preparation_authorized"] is True
    assert basis["construction_execution_authorized"] is False
    assert review["source_map_witness_chain_construction_packet_preparation_authorized"] is True
    assert review["source_map_witness_chain_construction_execution_authorized"] is False
    assert review["source_map_witness_chain_evidence_construction_authorized"] is False
    assert review["evidence_construction_authorized"] is False
    assert review["evidence_construction_executed"] is False


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_keeps_blockers_tracked() -> None:
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


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_no_closure_construction_or_movement() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["source_map_closure_claimed"] is False
    assert review["source_map_semantic_closure_authorized"] is False
    assert review["witness_chain_constructed"] is False
    assert review["source_map_witness_chain_evidence_constructed"] is False
    assert review["bounded_witness_chain_construction_executed"] is False
    assert review["remediation_execution_authorized"] is False
    assert review["remediation_executed"] is False
    assert review["broader_remediation_executed"] is False
    assert review["blocker_movement_authorized"] is False
    assert review["blocker_movement_registered"] is False
    assert review["blocker_fully_remediated"] is False
    assert review["documentation_prepared"] is False
    assert review["policy_adjudication_executed"] is False
    assert review["expert_re_review_executed"] is False


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_forbidden_effects_false() -> None:
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


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "tranche_004_source_map_witness_chain_construction_packet_preparation_only"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_ONLY_"
        "NO_CONSTRUCTION_EXECUTION_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_tranche_004_source_map_witness_chain_construction_packet": "selected",
        "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration": "deferred",
        "prepare_v01_alpha_tranche_004_source_map_evidence_gap_refinement_packet": "deferred",
    }


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_acceptance_and_determinism() -> None:
    review = _json(RESULT_REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01Tranche004SourceMapWitnessChainEvidencePacketResultReview" in index_text
    assert (
        "v01_tranche_004_source_map_witness_chain_evidence_packet_result_review_does_not_claim_closure"
        in index_text
    )
