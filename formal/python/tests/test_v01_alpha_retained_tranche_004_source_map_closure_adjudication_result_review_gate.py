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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_adjudication_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
    CLOSURE_ADJUDICATION_ANSWER,
    CLOSURE_ADJUDICATION_RESULT_CLASSIFICATION,
    DEFAULT_OUT as DEFAULT_CLOSURE_ADJUDICATION_PATH,
    EXECUTION_ID as CLOSURE_ADJUDICATION_ID,
    OUTCOME_ID as CLOSURE_ADJUDICATION_OUTCOME,
    REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_source_map_closure_adjudication_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004SourceMapClosureAdjudicationResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_files_exist() -> None:
    assert DEFAULT_CLOSURE_ADJUDICATION_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_consumes_execution_only() -> None:
    review = _json(DEFAULT_OUT)
    execution = _json(DEFAULT_CLOSURE_ADJUDICATION_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert (
        review["consumes_source_map_closure_adjudication_execution"]
        == CLOSURE_ADJUDICATION_ID
    )
    assert review["consumes_source_map_closure_adjudication_execution_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_20260523_v0.json"
    )
    assert execution["outcome_id"] == CLOSURE_ADJUDICATION_OUTCOME
    assert execution["selected_next_target"] == CONSUMED_TARGET
    assert (
        review["consumed_source_map_closure_adjudication_result_classification"]
        == CLOSURE_ADJUDICATION_RESULT_CLASSIFICATION
    )


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_accepts_authorization_only_for_registration_packet_preparation() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_scope"] == (
        "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_RESULT_"
        "ONLY_NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert review["source_map_closure_adjudication_result_reviewed"] is True
    assert review["source_map_closure_adjudication_result_accepted_by_review"] is True
    assert review["source_map_closure_authorization_decision_accepted_by_review"] is True
    assert review["source_map_closure_authorization_accepted_by_review"] is True
    assert (
        review[
            "source_map_closure_authorization_accepted_for_registration_packet_preparation_only"
        ]
        is True
    )
    assert review["source_map_closure_authorization_accepted_as_final_closure"] is False
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["result_classification_count"] == 1
    assert review["closure_adjudication_answer"] == CLOSURE_ADJUDICATION_ANSWER
    assert review["closure_adjudication_answer_accepted_by_review"] is True
    assert review["source_map_closure_authorized_pending_result_review"] is True
    assert review["source_map_closure_authorization_result_review_required"] is False
    assert review["source_map_closure_registration_packet_preparation_authorized"] is True
    assert review["source_map_closure_registration_packet_preparation_only"] is True
    assert review["source_map_closure_registration_packet_prepared"] is False
    assert review["source_map_closure_registration_authorized"] is False


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_reviews_all_requirements_without_registration() -> None:
    review = _json(DEFAULT_OUT)
    assert review["reviewed_closure_requirement_count"] == 7
    assert review["accepted_closure_requirement_count"] == 7
    assert review["adjudicated_closure_requirement_count"] == 7
    assert review["closure_adjudication_requirement_count"] == 7
    assert review["reviewed_authorization_requirement_count"] == 7
    assert review["accepted_authorization_requirement_count"] == 7
    assert review["reviewed_witness_chain_component_count"] == 7
    assert review["required_proof_surface_count"] == 7
    assert review["required_evidence_surface_count"] == 6
    assert review["closure_adjudication_success_criteria_count"] == 4
    assert review["closure_adjudication_failure_criteria_count"] == 4
    assert review["closure_adjudication_execution_boundary_count"] == 5
    assert review["closure_adjudication_execution_step_count"] == 5
    assert {
        row["execution_adjudication_status"]
        for row in review["reviewed_closure_requirements"]
    } == {"satisfies_source_map_closure_requirement_pending_result_review"}
    assert {
        row["result_review_status"] for row in review["reviewed_closure_requirements"]
    } == {"accepted_for_source_map_closure_registration_packet_preparation_only"}
    assert {
        row["closure_registration_status"]
        for row in review["reviewed_closure_requirements"]
    } == {"not_registered_by_result_review_alone"}


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_preserves_retained_blocker_and_release_hold() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert review["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == TRANCHE_003_STATUS
    assert review["tranche_004_status"] == TRANCHE_004_STATUS
    assert review["tranche_005_status"] == TRANCHE_005_STATUS
    assert review["tranche_006_status"] == TRANCHE_006_STATUS
    assert review["documented_dependency_nonblocking_tranche_count"] == 5
    assert review["retained_tranche_004_carry_forward"]["status"] == TRANCHE_004_STATUS
    assert review["required_future_route_for_tranche_004"] == TRANCHE_004_FUTURE_ROUTE
    assert review["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert review["tranche_004_status_moved_by_review"] is False
    assert review["tranche_004_status_moved"] is False
    assert review["tranche_004_retained_blocker_discharged"] is False
    assert review["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert review["release_readiness_held"] is True
    assert review["release_readiness_still_blocked"] is True
    assert review["release_readiness_proceed_authorized"] is False
    assert review["release_assembly_authorized"] is False
    assert review["release_packet_assembled"] is False
    assert review["v01_alpha_marked_ready"] is False


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_does_not_claim_closure_or_promotion() -> None:
    review = _json(DEFAULT_OUT)
    assert review["source_map_closure_achieved"] is False
    assert review["source_map_closure_authorized"] is False
    assert review["source_map_closure_claimed"] is False
    assert review["source_map_closure_registered"] is False
    assert review["source_map_closure_result_claimed_as_final_closure"] is False
    assert review["qft_gr_source_map_semantic_closure_claimed"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["qft_gr_seam_closure_authorized"] is False
    assert review["qft_gr_seam_closure_claimed"] is False
    assert review["blocker_movement_authorized"] is False
    assert review["blocker_movement_registered"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced"] is False
    assert review["proof_debt_reduced"] is False
    assert review["retained_assumptions_discharged"] is False
    assert review["phase2_authorized"] is False
    assert review["empirical_validation_authorized"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["publication_authorized"] is False
    assert review["master_action_promotion_authorized"] is False


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_forbidden_effects_false() -> None:
    review = _json(DEFAULT_OUT)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_selects_exactly_one_next_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "retained_tranche_004_source_map_closure_registration_packet_preparation_only"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_"
        "PACKET_ONLY_NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_"
        "PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        BLOCKER_MOVEMENT_ADJUDICATION_TARGET: "deferred",
        REFINED_AUTHORIZATION_ADJUDICATION_TARGET: "deferred",
        ASSEMBLE_RELEASE_PACKET_TARGET: "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_determinism() -> None:
    review = _json(DEFAULT_OUT)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_source_map_closure_adjudication_result_review(
        closure_adjudication_path=DEFAULT_CLOSURE_ADJUDICATION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_source_map_closure_adjudication_result_review(
        closure_adjudication_path=DEFAULT_CLOSURE_ADJUDICATION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_RESULT_REVIEW_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_gate.py",
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        CLOSURE_ADJUDICATION_RESULT_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004SourceMapClosureAdjudicationResultReview" in index_text
    assert (
        "v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_authorizes_closure_registration_packet_preparation_only"
        in index_text
    )
