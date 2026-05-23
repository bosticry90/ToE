from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review_report import (
    OUTCOME_ID as RESULT_REVIEW_OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as RESULT_REVIEW_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    BLOCKED_OBJECT,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_FUTURE_ROUTE,
    TRANCHE_004_STATUS,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    CONSTRUCTION_EXECUTION_TARGET,
    DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    FORBIDDEN_EFFECTS,
    MISSING_OBJECT,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    REFINED_RESEARCH_TARGET,
    SCHEMA_ID,
    build_construction_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004SourceMapWitnessChainConstructionPacketFromResearchCandidate.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

PROHIBITED_POSITIVE_PHRASES = [
    "witness chain constructed true",
    "source map closure claimed true",
    "QFT-GR seam closure claimed true",
    "release packet assembled true",
    "v0.1-alpha marked ready",
    "Lean theorem debt discharged true",
    "proof debt reduced true",
    "retained assumptions discharged true",
    "Phase 2 authorized true",
    "empirical validation authorized true",
    "publication authorized true",
    "master action promoted",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_construction_packet_from_research_candidate_files_exist() -> None:
    assert DEFAULT_ATTEMPT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_construction_packet_from_research_candidate_consumes_review() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_research_attempt_result_review"] == RESULT_REVIEW_ID
    assert packet["consumes_research_attempt_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_REVIEW_20260523_v0.json"
    )
    result_review = _json(DEFAULT_ATTEMPT_RESULT_REVIEW_PATH)
    assert result_review["outcome_id"] == RESULT_REVIEW_OUTCOME_ID
    assert result_review["selected_next_target"] == (
        "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate"
    )


def test_v01_alpha_retained_tranche_004_construction_packet_from_research_candidate_prepares_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["packet_scope"] == (
        "PREPARE_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_"
        "FROM_RESEARCH_CANDIDATE_ONLY_NO_WITNESS_CONSTRUCTION_SOURCE_MAP_CLOSURE_"
        "BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert packet["construction_packet_prepared"] is True
    assert packet["construction_packet_prepared_only"] is True
    assert packet["source_map_witness_chain_construction_packet_prepared"] is True
    assert (
        packet["source_map_witness_chain_construction_packet_prepared_from_research_candidate"]
        is True
    )
    assert packet["construction_execution_authorized_by_packet"] is False
    assert packet["source_map_witness_chain_construction_executed"] is False
    assert packet["witness_chain_constructed"] is False
    assert packet["source_map_witness_chain_constructed"] is False
    assert packet["accepted_input_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert packet["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert packet["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert packet["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert packet["blocked_object"] == BLOCKED_OBJECT
    assert packet["missing_object"] == MISSING_OBJECT


def test_v01_alpha_retained_tranche_004_construction_packet_from_research_candidate_carries_components() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["candidate_witness_chain_component_count"] == 7
    assert packet["required_proof_surface_count"] == 7
    assert packet["required_evidence_surface_count"] == 6
    assert packet["success_criteria_count"] == 4
    assert packet["failure_criteria_count"] == 5
    assert packet["construction_execution_boundary_count"] == 5
    components = packet["candidate_witness_chain_components"]
    assert {row["construction_packet_status"] for row in components} == {
        "candidate_input_only_not_constructed_by_packet"
    }
    assert all(row["candidate_surface_exists"] is True for row in components)
    assert all(row["candidate_result_review_surface_exists"] is True for row in components)
    assert "semantic_transport_link_map" in {
        row["evidence_id"] for row in packet["required_evidence_surfaces"]
    }


def test_v01_alpha_retained_tranche_004_construction_packet_from_research_candidate_preserves_hold() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_004_status"] == TRANCHE_004_STATUS
    assert packet["tranche_005_status"] == TRANCHE_005_STATUS
    assert packet["tranche_006_status"] == TRANCHE_006_STATUS
    assert packet["documented_dependency_nonblocking_tranche_count"] == 5
    assert packet["retained_tranche_004_carry_forward"]["status"] == TRANCHE_004_STATUS
    assert packet["required_future_route_for_tranche_004"] == TRANCHE_004_FUTURE_ROUTE
    assert packet["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert packet["release_readiness_held"] is True
    assert packet["release_readiness_still_blocked"] is True
    assert packet["release_readiness_proceed_authorized"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["release_packet_assembled"] is False
    assert packet["v01_alpha_marked_ready"] is False


def test_v01_alpha_retained_tranche_004_construction_packet_from_research_candidate_selects_review() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["post_packet_review_target"] == NEXT_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "source_map_witness_chain_construction_packet_from_research_candidate_"
        "result_review_only"
    )
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSTRUCTION_EXECUTION_TARGET: "deferred",
        REFINED_RESEARCH_TARGET: "deferred",
        ASSEMBLE_RELEASE_PACKET_TARGET: "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_construction_packet_from_research_candidate_forbidden_effects() -> None:
    packet = _json(DEFAULT_OUT)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert packet["source_map_closure_achieved"] is False
    assert packet["source_map_closure_authorized"] is False
    assert packet["source_map_closure_claimed"] is False
    assert packet["qft_gr_source_map_semantic_closure_claimed"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["qft_gr_seam_closure_authorized"] is False
    assert packet["qft_gr_seam_closure_claimed"] is False
    assert packet["tranche_004_status_moved"] is False
    assert packet["tranche_004_retained_blocker_discharged"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["phase2_authorized"] is False
    assert packet["empirical_validation_authorized"] is False
    assert packet["publication_authorized"] is False
    assert packet["master_action_promotion_authorized"] is False

    combined = json.dumps(packet, sort_keys=True) + "\n" + _read(ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_retained_tranche_004_construction_packet_from_research_candidate_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_construction_packet(
        result_review_path=DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_construction_packet(
        result_review_path=DEFAULT_ATTEMPT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_retained_tranche_004_construction_packet_from_research_candidate_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
        BLOCKED_OBJECT,
        MISSING_OBJECT,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004SourceMapWitnessChainConstructionPacketFromResearchCandidate" in index_text
    assert (
        "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_prepares_packet_only"
        in index_text
    )
