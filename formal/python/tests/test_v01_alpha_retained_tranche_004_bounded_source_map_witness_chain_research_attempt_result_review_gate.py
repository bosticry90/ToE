from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_report import (
    ATTEMPT_ID,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_ATTEMPT_PATH,
    OUTCOME_ID as ATTEMPT_OUTCOME_ID,
    RESEARCH_ATTEMPT_CLASSIFICATION,
)
from formal.python.tools.v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review_report import (
    DEFAULT_OUT,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_attempt_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004BoundedSourceMapWitnessChainResearchAttemptResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_result_review_files_exist() -> None:
    assert DEFAULT_ATTEMPT_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_result_review_consumes_attempt_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_bounded_source_map_witness_chain_research_attempt"] == ATTEMPT_ID
    assert review["consumes_bounded_source_map_witness_chain_research_attempt_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_20260523_v0.json"
    )
    attempt = _json(DEFAULT_ATTEMPT_PATH)
    assert attempt["outcome_id"] == ATTEMPT_OUTCOME_ID
    assert attempt["research_attempt_result_classification"] == RESEARCH_ATTEMPT_CLASSIFICATION


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_result_review_records_exact_classification() -> None:
    review = _json(DEFAULT_OUT)
    assert review["research_attempt_result_reviewed"] is True
    assert review["research_attempt_result_accepted"] is True
    assert review["research_attempt_result_accepted_as_partial_candidate_only"] is True
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["result_classification_count"] == 1
    assert (
        review[
            "partial_witness_chain_candidate_accepted_for_construction_packet_preparation_only"
        ]
        is True
    )
    assert review["partial_witness_chain_candidate_pending_review"] is False
    assert review["candidate_witness_chain_component_check_count"] == 7
    assert review["candidate_witness_chain_surface_found_count"] == 7
    for row in review["candidate_witness_chain_component_checks"]:
        assert row["surface_exists"] is True
        assert row["result_review_surface_exists"] is True
        assert row["attempt_status"] == "repo_local_candidate_surface_found_supplied_only_not_closure"


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_result_review_authorizes_preparation_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["construction_packet_preparation_authorized"] is True
    assert review["construction_packet_preparation_only"] is True
    assert review["source_map_witness_chain_construction_packet_prepared"] is False
    assert review["source_map_witness_chain_construction_executed"] is False
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "source_map_witness_chain_construction_packet_preparation_only"
    )
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_refined_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt": "deferred",
        "assemble_v01_alpha_release_packet": "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_result_review_preserves_nonclaim_boundary() -> None:
    review = _json(DEFAULT_OUT)
    assert review["tranche_004_status"] == "retained_release_blocking_source_map_blocker"
    assert review["release_readiness_held"] is True
    assert review["release_readiness_still_blocked"] is True
    assert review["release_readiness_proceed_authorized"] is False
    assert review["release_assembly_authorized"] is False
    assert review["release_assembly_authorized_by_review"] is False
    assert review["release_packet_assembled"] is False
    assert review["readiness_marking_authorized"] is False
    assert review["v01_alpha_marked_ready"] is False
    assert review["witness_chain_constructed"] is False
    assert review["source_map_witness_chain_constructed"] is False
    assert review["source_map_closure_authorized_by_review"] is False
    assert review["source_map_closure_claimed"] is False
    assert review["qft_gr_source_map_semantic_closure_claimed"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["qft_gr_seam_closure_authorized_by_review"] is False
    assert review["qft_gr_seam_closure_claimed"] is False
    assert review["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert review["tranche_004_status_moved_by_review"] is False
    assert review["tranche_004_status_moved"] is False
    assert review["tranche_004_retained_blocker_discharged"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced"] is False
    assert review["proof_debt_reduced"] is False
    assert review["retained_assumptions_discharged"] is False
    assert review["phase2_authorized"] is False
    assert review["empirical_validation_authorized"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["publication_authorized"] is False
    assert review["master_action_promotion_authorized"] is False
    assert sorted(review["forbidden_effect_status"]) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert review["forbidden_effect_status"][key] is False


def test_v01_alpha_retained_tranche_004_bounded_research_attempt_result_review_determinism_and_pinning() -> None:
    review = _json(DEFAULT_OUT)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    generated = build_attempt_result_review(
        attempt_path=DEFAULT_ATTEMPT_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated == review

    roadmap_text = _read(ROADMAP_PATH)
    for ref in [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_BOUNDED_SOURCE_MAP_WITNESS_CHAIN_RESEARCH_ATTEMPT_RESULT_REVIEW_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review_gate.py",
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        NEXT_TARGET,
    ]:
        assert ref in roadmap_text

    lean_text = _read(LEAN_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004BoundedSourceMapWitnessChainResearchAttemptResultReview" in index_text
    assert (
        "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review_accepts_partial_candidate_for_construction_packet_preparation_only"
        in index_text
    )
