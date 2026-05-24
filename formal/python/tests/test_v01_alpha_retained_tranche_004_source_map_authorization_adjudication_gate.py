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
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_RESULT_REVIEW_SELECTED_TARGET,
    OUTCOME_ID as PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as PACKET_RESULT_REVIEW_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_authorization_adjudication_report import (
    ADJUDICATION_ANSWER,
    ADJUDICATION_RESULT_CLASSIFICATION,
    ASSEMBLE_RELEASE_PACKET_TARGET,
    BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
    DEFAULT_OUT,
    EXECUTION_ID,
    EXECUTION_TARGET,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    REFINED_ADJUDICATION_PACKET_TARGET,
    SCHEMA_ID,
    build_source_map_authorization_adjudication,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_EXECUTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004SourceMapAuthorizationAdjudication.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_files_exist() -> None:
    assert DEFAULT_PACKET_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_EXECUTION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_consumes_packet_result_review_only() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["schema_id"] == SCHEMA_ID
    assert execution["execution_id"] == EXECUTION_ID
    assert execution["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert execution["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert execution["accepted"] is True
    assert execution["executed"] is True
    assert execution["outcome_id"] == OUTCOME_ID
    assert (
        execution[
            "consumes_source_map_authorization_adjudication_packet_result_review"
        ]
        == PACKET_RESULT_REVIEW_ID
    )
    assert execution[
        "consumes_source_map_authorization_adjudication_packet_result_review_pointer"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_PACKET_RESULT_REVIEW_20260523_v0.json"
    )
    packet_review = _json(DEFAULT_PACKET_RESULT_REVIEW_PATH)
    assert packet_review["outcome_id"] == PACKET_RESULT_REVIEW_OUTCOME
    assert packet_review["selected_next_target"] == EXPECTED_PACKET_RESULT_REVIEW_SELECTED_TARGET
    assert (
        execution["consumed_packet_result_review_classification"]
        == PACKET_RESULT_REVIEW_CLASSIFICATION
    )


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_answers_narrow_question_pending_review() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["execution_scope"] == (
        "EXECUTE_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
        "ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert execution["source_map_authorization_adjudication_execution_target"] == EXECUTION_TARGET
    assert execution["source_map_authorization_adjudication_executed"] is True
    assert execution["bounded_source_map_authorization_adjudication_executed"] is True
    assert execution["bounded_source_map_authorization_adjudication_execution_only"] is True
    assert (
        execution["source_map_authorization_adjudication_result_classification"]
        == ADJUDICATION_RESULT_CLASSIFICATION
    )
    assert execution["result_classification_count"] == 1
    assert execution["adjudication_result_classification_count"] == 1
    assert execution["adjudication_question"] == (
        "Does the accepted witness-chain construction satisfy the source-map "
        "semantic-closure authorization requirements?"
    )
    assert execution["adjudication_question_answered"] is True
    assert execution["adjudication_answer"] == ADJUDICATION_ANSWER
    assert execution["adjudication_answer_pending_result_review"] is True
    assert (
        execution[
            "source_map_authorization_requirements_satisfied_pending_result_review"
        ]
        is True
    )
    assert execution["source_map_closure_requirements_adjudicated"] is True
    assert execution["source_map_closure_authorization_result_review_required"] is True


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_adjudicates_all_requirements_without_closure() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["adjudication_requirement_count"] == 7
    assert execution["adjudicated_requirement_count"] == 7
    assert execution["reviewed_witness_chain_component_count"] == 7
    assert execution["accepted_witness_chain_component_count"] == 7
    assert execution["required_proof_surface_count"] == 7
    assert execution["required_evidence_surface_count"] == 6
    assert execution["adjudication_success_criteria_count"] == 4
    assert execution["adjudication_failure_criteria_count"] == 4
    assert execution["adjudication_execution_boundary_count"] == 5
    assert {
        row["adjudication_status"] for row in execution["adjudicated_requirements"]
    } == {"satisfies_source_map_authorization_requirement_pending_result_review"}
    assert all(
        row["result_review_required_before_closure"] is True
        for row in execution["adjudicated_requirements"]
    )
    assert [step["step_id"] for step in execution["adjudication_execution_steps"]] == [
        "adjudication_001_consume_packet_result_review",
        "adjudication_002_carry_accepted_witness_chain_components",
        "adjudication_003_evaluate_semantic_closure_authorization_requirements",
        "adjudication_004_preserve_result_review_and_closure_firewall",
        "adjudication_005_classify_result_pending_review",
    ]


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_preserves_retained_blocker_and_release_hold() -> None:
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


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_does_not_claim_closure_or_promotion() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["witness_chain_construction_accepted"] is True
    assert execution["source_map_witness_chain_construction_accepted"] is True
    assert execution["witness_chain_constructed"] is True
    assert execution["source_map_witness_chain_constructed"] is True
    assert execution["source_map_closure_authorization_decision_accepted_by_review"] is False
    assert execution["adjudication_result_accepted_by_review"] is False
    assert execution["adjudication_result_claimed_as_closure"] is False
    assert execution["source_map_closure_achieved"] is False
    assert execution["source_map_closure_authorized"] is False
    assert execution["source_map_closure_claimed"] is False
    assert execution["source_map_closure_registered"] is False
    assert execution["qft_gr_source_map_semantic_closure_claimed"] is False
    assert execution["qft_gr_seam_closed"] is False
    assert execution["qft_gr_seam_closure_authorized"] is False
    assert execution["qft_gr_seam_closure_claimed"] is False
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


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_forbidden_effects_false() -> None:
    execution = _json(DEFAULT_OUT)
    forbidden = execution["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_selects_exactly_one_next_target() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == (
        "retained_tranche_004_source_map_authorization_adjudication_result_review_only"
    )
    assert execution["selection_count"] == 1
    assert execution["next_action_scope"] == (
        "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_"
        "RESULT_ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in execution["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        BLOCKER_MOVEMENT_ADJUDICATION_TARGET: "deferred",
        REFINED_ADJUDICATION_PACKET_TARGET: "deferred",
        ASSEMBLE_RELEASE_PACKET_TARGET: "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_determinism() -> None:
    execution = _json(DEFAULT_OUT)
    for key, value in execution["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_source_map_authorization_adjudication(
        packet_result_review_path=DEFAULT_PACKET_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_source_map_authorization_adjudication(
        packet_result_review_path=DEFAULT_PACKET_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert execution == generated_1


def test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        EXECUTION_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_ADJUDICATION_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_source_map_authorization_adjudication_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_gate.py",
        OUTCOME_ID,
        ADJUDICATION_RESULT_CLASSIFICATION,
        PACKET_RESULT_REVIEW_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_EXECUTION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004SourceMapAuthorizationAdjudication" in index_text
    assert (
        "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_records_requirements_satisfied_pending_result_review"
        in index_text
    )
