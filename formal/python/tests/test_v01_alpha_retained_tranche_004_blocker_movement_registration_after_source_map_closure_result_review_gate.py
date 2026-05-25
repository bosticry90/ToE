from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_report import (
    DEFAULT_OUT as EXECUTION_PATH,
    EXECUTION_ID,
    OUTCOME_ID as EXECUTION_OUTCOME,
    REGISTERED_TRANCHE_004_STATUS,
    REGISTRATION_CLASSIFICATION as EXECUTION_CLASSIFICATION,
    TRANCHE_004_STATUS_PENDING_REVIEW,
)
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_report import (
    DEFAULT_OUT,
    DEPENDENCY_REMEDIATION_CLOSEOUT_STATUS,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    RELEASE_READINESS_STATUS,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_blocker_movement_registration_result_review_after_source_map_closure,
)
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_packet_after_source_map_closure_report import (
    ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS,
    PRIOR_TRANCHE_004_STATUS,
    PROPOSED_MOVEMENT,
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
        "after_source_map_closure_result_review_report.py"
    )
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004BlockerMovementRegistrationAfterSourceMapClosureResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_files_exist() -> None:
    assert EXECUTION_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_consumes_execution() -> None:
    review = _json(DEFAULT_OUT)
    execution = _json(EXECUTION_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_blocker_movement_registration_execution"] == EXECUTION_ID
    assert review["consumes_blocker_movement_registration_execution_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
        "AFTER_SOURCE_MAP_CLOSURE_20260523_v0.json"
    )
    assert execution["outcome_id"] == EXECUTION_OUTCOME
    assert review["consumed_blocker_movement_registration_classification"] == (
        EXECUTION_CLASSIFICATION
    )


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_accepts_exact_status() -> None:
    review = _json(DEFAULT_OUT)
    movement = review["registered_movement"]
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["result_classification_count"] == 1
    assert review["blocker_movement_registration_result_reviewed"] is True
    assert review["blocker_movement_registration_result_accepted"] is True
    assert review["documented_source_map_closed_nonblocking_status_accepted"] is True
    assert review["documented_source_map_closed_nonblocking_status_rejected"] is False
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert review["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert review["prior_tranche_004_status"] == PRIOR_TRANCHE_004_STATUS
    assert review["registered_tranche_004_status"] == REGISTERED_TRANCHE_004_STATUS
    assert review["accepted_tranche_004_status"] == REGISTERED_TRANCHE_004_STATUS
    assert review["tranche_004_status"] == REGISTERED_TRANCHE_004_STATUS
    assert (
        review["tranche_004_previous_pending_review_status"]
        == TRANCHE_004_STATUS_PENDING_REVIEW
    )
    assert review["tranche_004_status_pending_result_review"] is False
    assert movement["previous_status"] == PRIOR_TRANCHE_004_STATUS
    assert movement["registered_status"] == REGISTERED_TRANCHE_004_STATUS
    assert movement["status_after_execution"] == TRANCHE_004_STATUS_PENDING_REVIEW
    assert movement["registered_movement"] == PROPOSED_MOVEMENT


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_records_formal_movement_without_release_readiness() -> None:
    review = _json(DEFAULT_OUT)
    assert review["blocker_movement_registration_status"] == REGISTERED_TRANCHE_004_STATUS
    assert review["tranche_004_status_moved_by_execution"] is True
    assert review["tranche_004_status_moved_by_result_review"] is True
    assert review["tranche_004_status_moved"] is True
    assert review["tranche_004_formal_movement_accepted"] is True
    assert review["tranche_004_moved_to_documented_source_map_closed_nonblocking"] is True
    assert review["tranche_004_retained_blocker_discharged"] is True
    assert review["tranche_004_cleared_for_release_readiness"] is False
    assert review["release_readiness_decision_status"] == RELEASE_READINESS_STATUS
    assert review["release_readiness_held"] is True
    assert review["release_readiness_still_blocked"] is True
    assert review["release_readiness_proceed_authorized"] is False
    assert review["release_readiness_adjudication_prepared"] is False
    assert review["release_assembly_authorized"] is False
    assert review["release_packet_assembled"] is False
    assert review["readiness_marking_authorized"] is False
    assert review["v01_alpha_marked_ready"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_preserves_source_map_closure_evidence() -> None:
    review = _json(DEFAULT_OUT)
    assert (
        review["accepted_source_map_closure_registration"]
        == ACCEPTED_SOURCE_MAP_CLOSURE_REGISTRATION_STATUS
    )
    assert (
        review["source_map_closure_registration_status"]
        == SOURCE_MAP_CLOSURE_REGISTRATION_ACCEPTED_STATUS
    )
    assert review["registered_source_map_closure_accepted_by_review"] is True
    assert review["source_map_closure_registered"] is True
    assert review["final_source_map_closure_registered"] is True
    assert review["source_map_closure_authorized"] is True
    assert review["final_source_map_closure_authorized"] is True
    assert review["source_map_closure_achieved"] is True
    assert review["source_map_closure_claimed"] is False
    assert review["source_map_closure_external_truth_claimed"] is False
    assert review["source_map_closure_registration_external_truth_claimed"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_confirms_dependency_closeout_pending() -> None:
    review = _json(DEFAULT_OUT)
    documented = review["documented_dependency_nonblocking_tranches"]
    assert review["documented_dependency_nonblocking_tranche_count"] == 6
    assert [row["finding_id"] for row in documented] == [
        "V01-ALPHA-DEP-REM-001",
        "V01-ALPHA-DEP-REM-002",
        "V01-ALPHA-DEP-REM-003",
        TRANCHE_004_FINDING_ID,
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    assert documented[3]["status"] == REGISTERED_TRANCHE_004_STATUS
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == TRANCHE_003_STATUS
    assert review["tranche_005_status"] == TRANCHE_005_STATUS
    assert review["tranche_006_status"] == TRANCHE_006_STATUS
    assert (
        review["dependency_remediation_closeout_status"]
        == DEPENDENCY_REMEDIATION_CLOSEOUT_STATUS
    )
    assert review["dependency_remediation_blocker_queue_exhausted"] is True
    assert review["simple_dependency_remediation_queue_exhausted"] is True
    assert review["unresolved_dependency_remediation_tranches"] == []
    assert review["unresolved_dependency_remediation_tranche_count"] == 0
    assert review["dependency_remediation_closeout_preparation_authorized"] is True
    assert review["dependency_remediation_closeout_prepared"] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_carries_review_material() -> None:
    review = _json(DEFAULT_OUT)
    assert review["evidence_chain_count"] == 9
    assert review["movement_registration_criteria_count"] == 4
    assert review["registration_criteria_count"] == 4
    assert review["reviewed_closure_requirement_count"] == 7
    assert review["accepted_closure_requirement_count"] == 7
    assert review["reviewed_authorization_requirement_count"] == 7
    assert review["accepted_authorization_requirement_count"] == 7
    assert review["reviewed_witness_chain_component_count"] == 7
    assert review["forbidden_downstream_claim_count"] == 6
    assert review["blocker_movement_registration_step_count"] == 5


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_does_not_close_or_promote() -> None:
    review = _json(DEFAULT_OUT)
    assert review["qft_gr_source_map_semantic_closure_claimed"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["qft_gr_seam_closure_authorized"] is False
    assert review["qft_gr_seam_closure_claimed"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced"] is False
    assert review["proof_debt_reduced"] is False
    assert review["retained_assumptions_discharged"] is False
    assert review["phase2_authorized"] is False
    assert review["empirical_validation_authorized"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["publication_authorized"] is False
    assert review["master_action_promotion_authorized"] is False
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_selects_exactly_one_next_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "dependency_remediation_closeout_preparation_after_tranche_004_"
        "movement_only"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
        "MOVEMENT_ONLY_NO_RELEASE_READINESS_OR_QFT_GR_SEAM_CLOSURE"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "assemble_v01_alpha_release_packet": "not_authorized",
        "mark_v01_alpha_release_ready": "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_determinism() -> None:
    review = _json(DEFAULT_OUT)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_blocker_movement_registration_result_review_after_source_map_closure(
        execution_path=EXECUTION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_blocker_movement_registration_result_review_after_source_map_closure(
        execution_path=EXECUTION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_gate.py",
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        EXECUTION_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert (
        "V01RetainedTranche004BlockerMovementRegistrationAfterSourceMapClosureResultReview"
        in index_text
    )
    assert (
        "v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_accepts_documented_status"
        in index_text
    )
