from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_report import (
    ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS,
    DEFAULT_OUT,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIOR_TRANCHE_004_STATUS,
    PROPOSED_MOVEMENT,
    PROPOSED_TRANCHE_004_STATUS,
    SCHEMA_ID,
    build_blocker_movement_registration_packet_after_source_map_closure,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_FUTURE_ROUTE,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_registration_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as RESULT_REVIEW_ID,
    SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004BlockerMovementRegistrationPacketAfterSourceMapClosure.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_consumes_result_review() -> None:
    packet = _json(DEFAULT_OUT)
    result_review = _json(RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["packet_classification_count"] == 1
    assert (
        packet["consumes_source_map_closure_registration_result_review"]
        == RESULT_REVIEW_ID
    )
    assert packet["consumes_source_map_closure_registration_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_RESULT_REVIEW_20260523_v0.json"
    )
    assert result_review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert (
        packet["consumed_source_map_closure_registration_result_review_classification"]
        == RESULT_REVIEW_CLASSIFICATION
    )


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_prepares_movement_only() -> None:
    packet = _json(DEFAULT_OUT)
    proposal = packet["movement_proposal"]
    assert packet["packet_scope"] == (
        "PREPARE_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
        "AFTER_SOURCE_MAP_CLOSURE_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_"
        "PROMOTION"
    )
    assert packet["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert packet["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert packet["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert packet["prior_tranche_004_status"] == PRIOR_TRANCHE_004_STATUS
    assert packet["proposed_tranche_004_status"] == PROPOSED_TRANCHE_004_STATUS
    assert (
        packet["accepted_source_map_closure_registration"]
        == ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
    )
    assert packet["source_map_closure_registration_status"] == (
        SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
    )
    assert packet["proposed_movement"] == PROPOSED_MOVEMENT
    assert proposal["prior_status"] == PRIOR_TRANCHE_004_STATUS
    assert proposal["proposed_status"] == PROPOSED_TRANCHE_004_STATUS
    assert proposal["proposed_movement"] == PROPOSED_MOVEMENT
    assert proposal["movement_scope"] == "retained_tranche_004_source_map_blocker_only"
    assert proposal["requires_result_review_before_execution"] is True
    assert proposal["registers_movement_now"] is False
    assert proposal["moves_tranche_004_now"] is False
    assert proposal["clears_retained_blocker_now"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_carries_source_map_registration_evidence() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["registered_source_map_closure_accepted_by_review"] is True
    assert (
        packet[
            "registered_source_map_closure_accepted_for_blocker_movement_packet_preparation_only"
        ]
        is True
    )
    assert packet["source_map_closure_registered"] is True
    assert packet["final_source_map_closure_registered"] is True
    assert packet["source_map_closure_authorized"] is True
    assert packet["final_source_map_closure_authorized"] is True
    assert packet["source_map_closure_achieved"] is True
    assert packet["source_map_closure_claimed"] is False
    assert packet["source_map_closure_external_truth_claimed"] is False
    assert packet["source_map_closure_registration_external_truth_claimed"] is False
    assert packet["evidence_chain_count"] == 9
    assert packet["evidence_chain"][-1]["chain_id"] == (
        "source_map_closure_registration_result_review"
    )
    assert packet["registration_criteria_count"] == 4
    assert packet["reviewed_closure_requirement_count"] == 7
    assert packet["accepted_closure_requirement_count"] == 7
    assert packet["reviewed_authorization_requirement_count"] == 7
    assert packet["accepted_authorization_requirement_count"] == 7
    assert packet["reviewed_witness_chain_component_count"] == 7
    assert packet["forbidden_downstream_claim_count"] == 6


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_preserves_tranche_and_release_hold() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_004_status"] == PRIOR_TRANCHE_004_STATUS
    assert packet["tranche_005_status"] == TRANCHE_005_STATUS
    assert packet["tranche_006_status"] == TRANCHE_006_STATUS
    assert packet["documented_dependency_nonblocking_tranche_count"] == 5
    assert packet["retained_tranche_004_carry_forward"]["status"] == (
        PRIOR_TRANCHE_004_STATUS
    )
    assert packet["required_future_route_for_tranche_004"] == TRANCHE_004_FUTURE_ROUTE
    assert packet["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert packet["release_readiness_held"] is True
    assert packet["release_readiness_still_blocked"] is True
    assert packet["release_readiness_proceed_authorized"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_does_not_execute_or_promote() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocker_movement_registration_packet_prepared"] is True
    assert (
        packet["blocker_movement_registration_packet_prepared_after_source_map_closure"]
        is True
    )
    assert packet["blocker_movement_registration_packet_result_review_required"] is True
    assert packet["blocker_movement_registration_packet_result_review_authorized"] is True
    assert packet["blocker_movement_registration_execution_authorized"] is False
    assert packet["blocker_movement_authorized"] is False
    assert packet["blocker_movement_registered"] is False
    assert packet["tranche_004_status_moved_by_packet"] is False
    assert packet["tranche_004_status_moved"] is False
    assert packet["tranche_004_retained_blocker_discharged"] is False
    assert (
        packet["tranche_004_moved_to_documented_source_map_closed_nonblocking"]
        is False
    )
    assert packet["qft_gr_source_map_semantic_closure_claimed"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["qft_gr_seam_closure_authorized"] is False
    assert packet["qft_gr_seam_closure_claimed"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["release_packet_assembled"] is False
    assert packet["readiness_marking_authorized"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["phase2_authorized"] is False
    assert packet["empirical_validation_authorized"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["publication_authorized"] is False
    assert packet["master_action_promotion_authorized"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_forbidden_effects_false() -> None:
    packet = _json(DEFAULT_OUT)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_selects_exactly_one_next_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "retained_tranche_004_blocker_movement_registration_packet_after_"
        "source_map_closure_result_review_only"
    )
    assert packet["selection_count"] == 1
    assert packet["next_action_scope"] == (
        "REVIEW_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
        "AFTER_SOURCE_MAP_CLOSURE_RESULT_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_"
        "RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "assemble_v01_alpha_release_packet": "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_blocker_movement_registration_packet_after_source_map_closure(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_blocker_movement_registration_packet_after_source_map_closure(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_AFTER_SOURCE_MAP_CLOSURE_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_gate.py",
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        PROPOSED_MOVEMENT,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004BlockerMovementRegistrationPacketAfterSourceMapClosure" in index_text
    assert (
        "v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_does_not_move_tranche_004"
        in index_text
    )
