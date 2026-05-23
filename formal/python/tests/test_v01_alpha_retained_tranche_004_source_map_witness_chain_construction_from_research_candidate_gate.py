from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    CONSTRUCTION_RESULT_CLASSIFICATION,
    CONSTRUCTION_TARGET,
    DEFAULT_OUT,
    EXECUTION_TARGET,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    REFINED_RESEARCH_TARGET,
    SCHEMA_ID,
    SOURCE_MAP_ADJUDICATION_TARGET,
    ATTEMPT_ID,
    build_construction_execution,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as RESULT_REVIEW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_EXECUTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004SourceMapWitnessChainConstructionFromResearchCandidate.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_files_exist() -> None:
    assert DEFAULT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_EXECUTION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_consumes_result_review_only() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["schema_id"] == SCHEMA_ID
    assert execution["attempt_id"] == ATTEMPT_ID
    assert execution["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert execution["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert execution["accepted"] is True
    assert execution["executed"] is True
    assert execution["outcome_id"] == OUTCOME_ID
    assert execution["consumes_construction_packet_result_review"] == RESULT_REVIEW_ID
    assert execution["consumes_construction_packet_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_FROM_RESEARCH_CANDIDATE_RESULT_REVIEW_20260523_v0.json"
    )
    result_review = _json(DEFAULT_RESULT_REVIEW_PATH)
    assert result_review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert result_review["selected_next_target"] == EXECUTION_TARGET


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_executes_bounded_attempt_only() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["execution_scope"] == (
        "EXECUTE_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_"
        "RESEARCH_CANDIDATE_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_"
        "RELEASE_PROMOTION"
    )
    assert execution["construction_target"] == CONSTRUCTION_TARGET
    assert execution["construction_execution_target"] == EXECUTION_TARGET
    assert execution["source_map_witness_chain_construction_executed"] is True
    assert (
        execution["source_map_witness_chain_construction_executed_from_research_candidate"]
        is True
    )
    assert execution["bounded_construction_execution_executed"] is True
    assert execution["bounded_construction_execution_only"] is True
    assert execution["construction_result_classification"] == (
        CONSTRUCTION_RESULT_CLASSIFICATION
    )
    assert execution["result_classification_count"] == 1
    assert execution["construction_result_classification_count"] == 1
    assert len(execution["construction_execution_steps"]) == 5
    assert [step["step_id"] for step in execution["construction_execution_steps"]] == [
        "construction_001_bind_accepted_result_review_authorization",
        "construction_002_carry_candidate_component_set",
        "construction_003_construct_candidate_witness_chain_ordering",
        "construction_004_preserve_closure_and_release_firewall",
        "construction_005_classify_result_pending_review",
    ]


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_records_pending_review_not_closure() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["candidate_witness_chain_constructed_pending_result_review"] is True
    assert execution["witness_chain_constructed_pending_result_review"] is True
    assert execution["source_map_witness_chain_constructed_pending_result_review"] is True
    assert execution["witness_chain_constructed"] is False
    assert execution["source_map_witness_chain_constructed"] is False
    assert execution["witness_chain_constructed_claimed"] is False
    assert execution["source_map_witness_chain_constructed_claimed"] is False
    assert execution["construction_result_claimed"] is False
    assert execution["source_map_closure_achieved"] is False
    assert execution["source_map_closure_authorized"] is False
    assert execution["source_map_closure_claimed"] is False
    assert execution["qft_gr_source_map_semantic_closure_claimed"] is False
    assert execution["qft_gr_seam_closed"] is False
    assert execution["qft_gr_seam_closure_authorized"] is False
    assert execution["qft_gr_seam_closure_claimed"] is False


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_constructs_candidate_components_pending_review() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["candidate_witness_chain_component_count"] == 7
    assert execution["constructed_witness_chain_component_count"] == 7
    assert execution["required_witness_chain_component_count"] == 7
    assert execution["required_proof_surface_count"] == 7
    assert execution["required_evidence_surface_count"] == 6
    assert execution["success_criteria_count"] == 4
    assert execution["failure_criteria_count"] == 5
    assert execution["construction_execution_boundary_count"] == 5
    assert {
        row["construction_status"]
        for row in execution["constructed_witness_chain_components"]
    } == {"constructed_candidate_pending_result_review"}
    assert all(
        row["review_required_before_closure"] is True
        for row in execution["constructed_witness_chain_components"]
    )
    assert "weak_curvature_source_identification" in {
        row["component_id"] for row in execution["constructed_witness_chain_components"]
    }


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_preserves_release_hold_and_retained_blocker() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert execution["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert execution["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert execution["tranche_001_status"] == TRANCHE_001_STATUS
    assert execution["tranche_002_status"] == TRANCHE_002_STATUS
    assert execution["tranche_003_status"] == TRANCHE_003_STATUS
    assert execution["tranche_004_status"] == TRANCHE_004_STATUS
    assert execution["tranche_005_status"] == TRANCHE_005_STATUS
    assert execution["tranche_006_status"] == TRANCHE_006_STATUS
    assert execution["documented_dependency_nonblocking_tranche_count"] == 5
    assert execution["retained_tranche_004_carry_forward"]["status"] == TRANCHE_004_STATUS
    assert execution["required_future_route_for_tranche_004"] == TRANCHE_004_FUTURE_ROUTE
    assert execution["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert execution["tranche_004_status_moved_by_execution"] is False
    assert execution["tranche_004_status_moved"] is False
    assert execution["tranche_004_retained_blocker_discharged"] is False
    assert execution["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert execution["release_readiness_held"] is True
    assert execution["release_readiness_still_blocked"] is True
    assert execution["release_readiness_proceed_authorized"] is False
    assert execution["release_assembly_authorized"] is False
    assert execution["release_packet_assembled"] is False
    assert execution["v01_alpha_marked_ready"] is False


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_no_release_theorem_phase_empirical_publication_or_master_promotion() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["blocker_movement_authorized"] is False
    assert execution["blocker_movement_registered"] is False
    assert execution["lean_theorem_debt_discharged"] is False
    assert execution["axiom_spec_backed_debt_reduced"] is False
    assert execution["proof_debt_reduced"] is False
    assert execution["retained_assumptions_discharged"] is False
    assert execution["phase2_authorized"] is False
    assert execution["empirical_validation_authorized"] is False
    assert execution["empirical_validation_claimed"] is False
    assert execution["publication_authorized"] is False
    assert execution["master_action_promotion_authorized"] is False


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_forbidden_effects_false() -> None:
    execution = _json(DEFAULT_OUT)
    forbidden = execution["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_selects_exactly_one_next_target() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == (
        "retained_tranche_004_source_map_witness_chain_construction_from_research_"
        "candidate_result_review_only"
    )
    assert execution["selection_count"] == 1
    assert execution["next_action_scope"] == (
        "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_"
        "RESEARCH_CANDIDATE_RESULT_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_"
        "RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in execution["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        SOURCE_MAP_ADJUDICATION_TARGET: "deferred",
        REFINED_RESEARCH_TARGET: "deferred",
        ASSEMBLE_RELEASE_PACKET_TARGET: "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_determinism() -> None:
    execution = _json(DEFAULT_OUT)
    for key, value in execution["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_construction_execution(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_construction_execution(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert execution == generated_1


def test_v01_alpha_retained_tranche_004_construction_from_research_candidate_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        ATTEMPT_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_FROM_RESEARCH_CANDIDATE_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_gate.py",
        OUTCOME_ID,
        CONSTRUCTION_RESULT_CLASSIFICATION,
        RESULT_REVIEW_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_EXECUTION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert (
        "V01RetainedTranche004SourceMapWitnessChainConstructionFromResearchCandidate"
        in index_text
    )
    assert (
        "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_records_witness_chain_constructed_pending_result_review"
        in index_text
    )
