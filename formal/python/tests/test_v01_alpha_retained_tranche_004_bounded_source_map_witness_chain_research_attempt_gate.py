from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_report import (
    ATTEMPT_ID,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    RESEARCH_ATTEMPT_CLASSIFICATION,
    SCHEMA_ID,
    build_attempt,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_report.py"
)
PACKET_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_20260522_v0.json"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004BoundedSourceMapWitnessChainResearchAttempt.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_files_exist() -> None:
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert PACKET_RESULT_REVIEW_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_consumes_packet_review() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert attempt["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert attempt["accepted"] is True
    assert attempt["outcome_id"] == OUTCOME_ID
    assert attempt["consumes_bounded_source_map_witness_chain_research_packet_result_review"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_PACKET_RESULT_REVIEW_v0"
    )


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_records_exact_classification() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["research_attempt_executed"] is True
    assert attempt["bounded_source_map_witness_chain_research_attempt_executed"] is True
    assert attempt["research_attempt_result_classification"] == RESEARCH_ATTEMPT_CLASSIFICATION
    assert attempt["result_classification_count"] == 1
    assert attempt["partial_witness_chain_candidate_produced"] is True
    assert attempt["partial_witness_chain_candidate_pending_review"] is True
    assert attempt["candidate_witness_chain_component_check_count"] == 7
    assert attempt["candidate_witness_chain_surface_found_count"] == 7
    for row in attempt["candidate_witness_chain_component_checks"]:
        assert row["surface_exists"] is True
        assert row["result_review_surface_exists"] is True
        assert row["attempt_status"] == "repo_local_candidate_surface_found_supplied_only_not_closure"


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_preserves_nonclaim_boundary() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["tranche_004_status"] == "retained_release_blocking_source_map_blocker"
    assert attempt["release_readiness_held"] is True
    assert attempt["release_readiness_still_blocked"] is True
    assert attempt["release_assembly_authorized"] is False
    assert attempt["release_packet_assembled"] is False
    assert attempt["witness_chain_constructed"] is False
    assert attempt["source_map_witness_chain_constructed"] is False
    assert attempt["source_map_closure_claimed"] is False
    assert attempt["qft_gr_source_map_semantic_closure_claimed"] is False
    assert attempt["qft_gr_seam_closed"] is False
    assert attempt["qft_gr_seam_closure_claimed"] is False
    assert attempt["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert attempt["tranche_004_status_moved_by_attempt"] is False
    assert attempt["tranche_004_retained_blocker_discharged"] is False
    assert attempt["lean_theorem_debt_discharged"] is False
    assert attempt["proof_debt_reduced"] is False
    assert attempt["retained_assumptions_discharged"] is False
    assert attempt["phase2_authorized"] is False
    assert attempt["empirical_validation_authorized"] is False
    assert attempt["master_action_promotion_authorized"] is False
    assert sorted(attempt["forbidden_effect_status"]) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert attempt["forbidden_effect_status"][key] is False


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_selects_one_review_target() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["selected_next_target_kind"] == (
        "bounded_source_map_witness_chain_research_attempt_result_review_only"
    )
    assert attempt["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in attempt["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate": "deferred",
        "prepare_refined_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt": "deferred",
        "assemble_v01_alpha_release_packet": "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_determinism_and_pinning() -> None:
    attempt = _json(DEFAULT_OUT)
    for key, value in attempt["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    generated = build_attempt(
        packet_result_review_path=PACKET_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated == attempt

    roadmap_text = _read(ROADMAP_PATH)
    for ref in [
        ATTEMPT_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_gate.py",
        OUTCOME_ID,
        RESEARCH_ATTEMPT_CLASSIFICATION,
        NEXT_TARGET,
    ]:
        assert ref in roadmap_text

    lean_text = _read(LEAN_ATTEMPT_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004BoundedSourceMapWitnessChainResearchAttempt" in index_text
    assert (
        "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_records_partial_candidate_pending_review"
        in index_text
    )
