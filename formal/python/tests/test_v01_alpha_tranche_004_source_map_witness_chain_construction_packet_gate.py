from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_tranche_004_source_map_witness_chain_construction_packet_report import (
    BLOCKER_REASON,
    CANDIDATE_CONSTRUCTION_ROUTE,
    CURRENT_BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    FAILURE_CRITERIA,
    LEAN_AXIOMS_USED,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    POST_CONSTRUCTION_REVIEW_TARGET,
    PROJECT_AXIOMS_USED,
    REQUIRED_DOCUMENTATION_SURFACES,
    REQUIRED_LEAN_THEORY_SURFACES,
    REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
    REQUIRED_WITNESS_CHAIN_COMPONENTS,
    SCHEMA_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    SUCCESS_CRITERIA,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    build_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_REVIEW_20260515_v0.json"
)
PACKET_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_tranche_004_source_map_witness_chain_construction_packet_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01Tranche004SourceMapWitnessChainConstructionPacket.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "source_map_closure_claimed",
    "source_map_semantic_closure_authorized",
    "qft_gr_seam_closed",
    "witness_chain_constructed",
    "source_map_witness_chain_evidence_constructed",
    "source_map_witness_chain_evidence_construction_authorized",
    "source_map_witness_chain_construction_executed",
    "evidence_construction_executed",
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


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert PACKET_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_consumes_result_review() -> None:
    packet = _json(PACKET_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_witness_chain_evidence_packet_result_review"] == (
        "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_REVIEW_v0"
    )
    assert packet["consumes_witness_chain_evidence_packet_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_scope() -> None:
    packet = _json(PACKET_PATH)
    assert packet["packet_scope"] == (
        "PREPARE_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_ONLY_"
        "NO_WITNESS_CONSTRUCTION_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_004_status"] == (
        "construction_packet_prepared_source_map_closure_still_unauthorized_pending_"
        "construction_packet_result_review"
    )
    assert packet["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert packet["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert packet["selected_dependency"] == SELECTED_DEPENDENCY
    assert packet["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert packet["source_map_witness_chain_construction_packet_prepared"] is True


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_preserves_blocker_and_lean_posture() -> None:
    packet = _json(PACKET_PATH)
    assert packet["current_blocker"] == CURRENT_BLOCKER
    assert packet["blocker_reason"] == BLOCKER_REASON
    assert packet["source_map_authorization_status"]["authorization_status"] == CURRENT_BLOCKER
    assert packet["source_map_authorization_status"]["full_source_map_semantic_closure_authorized"] is False
    assert packet["source_map_authorization_status"]["not_authorized_reason"] == BLOCKER_REASON
    assert packet["lean_audit_result"]["parsed_axioms"] == LEAN_AXIOMS_USED
    assert packet["lean_audit_result"]["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert packet["lean_audit_result"]["project_axiom_count"] == 0
    assert packet["lean_audit_result"]["depends_on_no_axioms"] is True
    assert packet["project_axioms_used"] == PROJECT_AXIOMS_USED


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_prepares_route_only() -> None:
    packet = _json(PACKET_PATH)
    scope = packet["construction_packet_scope"]
    assert scope["scope_kind"] == "SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_PREPARATION_ONLY"
    assert scope["current_blocker"] == CURRENT_BLOCKER
    assert scope["blocker_reason"] == BLOCKER_REASON
    assert packet["required_witness_chain_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
    assert packet["required_source_map_semantic_closure_conditions"] == (
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
    )
    assert packet["candidate_construction_route"] == CANDIDATE_CONSTRUCTION_ROUTE
    assert len(packet["candidate_construction_route"]) == 5
    for step in packet["candidate_construction_route"]:
        assert step["execution_authorized_by_packet"] is False


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_records_surfaces_and_criteria() -> None:
    packet = _json(PACKET_PATH)
    assert packet["required_lean_theory_surfaces"] == REQUIRED_LEAN_THEORY_SURFACES
    assert packet["required_documentation_surfaces"] == REQUIRED_DOCUMENTATION_SURFACES
    assert packet["success_criteria"] == SUCCESS_CRITERIA
    assert packet["failure_criteria"] == FAILURE_CRITERIA
    assert "source_map_closure_is_claimed_by_preparation_packet" in packet["failure_criteria"]
    assert any(
        row["path"].endswith("QFT_GR_SourceMapEligibilityLadderSummary.lean")
        for row in packet["required_lean_theory_surfaces"]
    )
    assert packet["post_construction_review_target"] == POST_CONSTRUCTION_REVIEW_TARGET


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_boundaries() -> None:
    packet = _json(PACKET_PATH)
    boundaries = packet["construction_execution_boundaries"]
    assert boundaries["construction_execution_authorized_by_this_packet"] is False
    assert boundaries["future_execution_requires_packet_result_review"] is True
    assert boundaries["source_map_authorization_change_allowed_by_this_packet"] is False
    assert boundaries["source_map_closure_claim_allowed_by_this_packet"] is False
    assert boundaries["blocker_movement_allowed_by_this_packet"] is False
    assert boundaries["release_readiness_allowed_by_this_packet"] is False
    assert boundaries["theorem_debt_discharge_allowed_by_this_packet"] is False
    assert boundaries["phase2_or_seam_closure_allowed_by_this_packet"] is False


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_keeps_blockers_tracked() -> None:
    packet = _json(PACKET_PATH)
    rows = packet["release_blocking_obligations_carry_forward"]
    assert packet["release_blocking_obligation_count"] == 3
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS
    selected = packet["selected_release_blocking_obligation"]
    assert selected["dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY
    assert selected["dependency_class"] == SELECTED_DEPENDENCY_CLASS
    for row in rows:
        assert row["modified_by_tranche_003"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_003"


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_no_construction_closure_or_movement() -> None:
    packet = _json(PACKET_PATH)
    assert packet["source_map_closure_claimed"] is False
    assert packet["source_map_semantic_closure_authorized"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["witness_chain_constructed"] is False
    assert packet["source_map_witness_chain_evidence_constructed"] is False
    assert packet["source_map_witness_chain_evidence_construction_authorized"] is False
    assert packet["source_map_witness_chain_construction_executed"] is False
    assert packet["evidence_construction_executed"] is False
    assert packet["remediation_execution_authorized"] is False
    assert packet["remediation_executed"] is False
    assert packet["blocker_movement_authorized"] is False
    assert packet["blocker_movement_registered"] is False
    assert packet["blocker_fully_remediated"] is False


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_forbidden_effects_false() -> None:
    packet = _json(PACKET_PATH)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert packet["release_packet_assembled"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["validation_claim_authorized"] is False


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_next_target() -> None:
    packet = _json(PACKET_PATH)
    assert packet["post_packet_review_target"] == NEXT_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "tranche_004_source_map_witness_chain_construction_packet_result_review_only"
    )
    assert packet["selection_count"] == 1
    assert packet["next_action_scope"] == (
        "REVIEW_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_ONLY_"
        "NO_CONSTRUCTION_EXECUTION_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        "review_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_result": "selected",
        "execute_v01_alpha_tranche_004_source_map_witness_chain_construction": "deferred",
        "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration": "deferred",
    }


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_acceptance_and_determinism() -> None:
    packet = _json(PACKET_PATH)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_20260515_v0.json",
        "formal/python/tools/v01_alpha_tranche_004_source_map_witness_chain_construction_packet_report.py",
        "formal/python/tests/test_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01Tranche004SourceMapWitnessChainConstructionPacket" in index_text
    assert (
        "v01_tranche_004_source_map_witness_chain_construction_packet_does_not_construct_witness_chain"
        in index_text
    )
