from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_report import (
    DEFAULT_OUT,
    EXECUTION_ID,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    REGISTERED_TRANCHE_004_STATUS,
    REGISTRATION_CLASSIFICATION,
    SCHEMA_ID,
    TRANCHE_004_STATUS_PENDING_REVIEW,
    build_blocker_movement_registration_after_source_map_closure,
)
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_report import (
    ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS,
    PRIOR_TRANCHE_004_STATUS,
    PROPOSED_MOVEMENT,
)
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_result_review_report import (
    DEFAULT_OUT as PACKET_RESULT_REVIEW_PATH,
    OUTCOME_ID as PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as PACKET_RESULT_REVIEW_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_registration_result_review_report import (
    SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / (
        "v01_alpha_retained_tranche_004_blocker_movement_registration_"
        "after_source_map_closure_report.py"
    )
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_EXECUTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004BlockerMovementRegistrationAfterSourceMapClosure.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_files_exist() -> None:
    assert PACKET_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_EXECUTION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_consumes_result_review() -> None:
    execution = _json(DEFAULT_OUT)
    review = _json(PACKET_RESULT_REVIEW_PATH)
    assert execution["schema_id"] == SCHEMA_ID
    assert execution["execution_id"] == EXECUTION_ID
    assert execution["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert execution["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert execution["accepted"] is True
    assert execution["executed"] is True
    assert execution["outcome_id"] == OUTCOME_ID
    assert execution[
        "consumes_blocker_movement_registration_packet_result_review"
    ] == PACKET_RESULT_REVIEW_ID
    assert execution[
        "consumes_blocker_movement_registration_packet_result_review_pointer"
    ] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_PACKET_"
        "AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_20260523_v0.json"
    )
    assert review["outcome_id"] == PACKET_RESULT_REVIEW_OUTCOME
    assert execution[
        "consumed_blocker_movement_registration_packet_result_review_classification"
    ] == PACKET_RESULT_REVIEW_CLASSIFICATION


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_registers_only_tranche_004() -> None:
    execution = _json(DEFAULT_OUT)
    movement = execution["registered_movement"]
    assert execution["execution_scope"] == (
        "EXECUTE_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_"
        "SOURCE_MAP_CLOSURE_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert execution["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert execution["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert execution["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert movement["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert movement["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert movement["previous_status"] == PRIOR_TRANCHE_004_STATUS
    assert movement["registered_status"] == REGISTERED_TRANCHE_004_STATUS
    assert movement["status_after_execution"] == TRANCHE_004_STATUS_PENDING_REVIEW
    assert movement["registered_movement"] == PROPOSED_MOVEMENT
    assert movement["movement_scope"] == "retained_tranche_004_source_map_blocker_only"
    assert movement["registered_by_this_execution"] is True
    assert movement["requires_result_review_for_formal_acceptance"] is True


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_records_exact_status_pending_review() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["prior_tranche_004_status"] == PRIOR_TRANCHE_004_STATUS
    assert execution["registered_tranche_004_status"] == REGISTERED_TRANCHE_004_STATUS
    assert execution["tranche_004_status"] == TRANCHE_004_STATUS_PENDING_REVIEW
    assert (
        execution["tranche_004_status_pending_result_review"]
        == TRANCHE_004_STATUS_PENDING_REVIEW
    )
    assert execution["blocker_movement_registration_executed"] is True
    assert execution["blocker_movement_registered"] is True
    assert execution["blocker_movement_registration_status"] == (
        TRANCHE_004_STATUS_PENDING_REVIEW
    )
    assert execution["blocker_movement_registration_result_classification"] == (
        REGISTRATION_CLASSIFICATION
    )
    assert execution["blocker_movement_registration_result_classification_count"] == 1
    assert execution["blocker_movement_registration_result_review_required"] is True
    assert execution["blocker_movement_registration_result_review_authorized"] is True
    assert execution["tranche_004_status_moved_by_execution"] is True
    assert execution["tranche_004_status_moved"] is True
    assert (
        execution["tranche_004_moved_to_documented_source_map_closed_nonblocking"]
        is True
    )
    assert execution["tranche_004_formal_movement_accepted"] is False
    assert execution["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_preserves_source_map_closure_evidence() -> None:
    execution = _json(DEFAULT_OUT)
    assert (
        execution["accepted_source_map_closure_registration"]
        == ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
    )
    assert (
        execution["source_map_closure_registration_status"]
        == SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
    )
    assert execution["registered_source_map_closure_accepted_by_review"] is True
    assert execution["source_map_closure_registered"] is True
    assert execution["final_source_map_closure_registered"] is True
    assert execution["source_map_closure_authorized"] is True
    assert execution["final_source_map_closure_authorized"] is True
    assert execution["source_map_closure_achieved"] is True
    assert execution["source_map_closure_claimed"] is False
    assert execution["source_map_closure_external_truth_claimed"] is False
    assert execution["source_map_closure_registration_external_truth_claimed"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_carries_evidence_and_release_hold() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["evidence_chain_count"] == 9
    assert execution["movement_registration_criteria_count"] == 4
    assert execution["registration_criteria_count"] == 4
    assert execution["reviewed_closure_requirement_count"] == 7
    assert execution["accepted_closure_requirement_count"] == 7
    assert execution["reviewed_authorization_requirement_count"] == 7
    assert execution["accepted_authorization_requirement_count"] == 7
    assert execution["reviewed_witness_chain_component_count"] == 7
    assert execution["forbidden_downstream_claim_count"] == 6
    assert execution["blocker_movement_registration_step_count"] == 5
    assert execution["tranche_001_status"] == TRANCHE_001_STATUS
    assert execution["tranche_002_status"] == TRANCHE_002_STATUS
    assert execution["tranche_003_status"] == TRANCHE_003_STATUS
    assert execution["tranche_005_status"] == TRANCHE_005_STATUS
    assert execution["tranche_006_status"] == TRANCHE_006_STATUS
    assert execution["documented_dependency_nonblocking_tranche_count"] == 5
    assert execution["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert execution["release_readiness_held"] is True
    assert execution["release_readiness_still_blocked"] is True
    assert execution["release_readiness_proceed_authorized"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_does_not_close_or_promote() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["qft_gr_source_map_semantic_closure_claimed"] is False
    assert execution["qft_gr_seam_closed"] is False
    assert execution["qft_gr_seam_closure_authorized"] is False
    assert execution["qft_gr_seam_closure_claimed"] is False
    assert execution["release_assembly_authorized"] is False
    assert execution["release_packet_assembled"] is False
    assert execution["readiness_marking_authorized"] is False
    assert execution["v01_alpha_marked_ready"] is False
    assert execution["lean_theorem_debt_discharged"] is False
    assert execution["axiom_spec_backed_debt_reduced"] is False
    assert execution["proof_debt_reduced"] is False
    assert execution["retained_assumptions_discharged"] is False
    assert execution["phase2_authorized"] is False
    assert execution["empirical_validation_authorized"] is False
    assert execution["empirical_validation_claimed"] is False
    assert execution["publication_authorized"] is False
    assert execution["master_action_promotion_authorized"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_forbidden_effects_false() -> None:
    execution = _json(DEFAULT_OUT)
    forbidden = execution["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_selects_exactly_one_next_target() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == (
        "retained_tranche_004_blocker_movement_registration_result_review_"
        "after_source_map_closure_only"
    )
    assert execution["selection_count"] == 1
    assert execution["next_action_scope"] == (
        "REVIEW_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_"
        "SOURCE_MAP_CLOSURE_RESULT_ONLY_NO_QFT_GR_SEAM_CLOSURE_OR_RELEASE_"
        "PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in execution["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "assemble_v01_alpha_release_packet": "not_authorized",
        "mark_v01_alpha_release_ready": "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_determinism() -> None:
    execution = _json(DEFAULT_OUT)
    for key, value in execution["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_blocker_movement_registration_after_source_map_closure(
        packet_result_review_path=PACKET_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_blocker_movement_registration_after_source_map_closure(
        packet_result_review_path=PACKET_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert execution == generated_1


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        EXECUTION_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_SOURCE_MAP_CLOSURE_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_gate.py",
        OUTCOME_ID,
        REGISTRATION_CLASSIFICATION,
        PACKET_RESULT_REVIEW_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_EXECUTION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004BlockerMovementRegistrationAfterSourceMapClosure" in index_text
    assert (
        "v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_registers_tranche_004_only"
        in index_text
    )
