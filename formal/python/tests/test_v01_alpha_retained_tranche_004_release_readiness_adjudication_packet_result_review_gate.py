from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_report import (
    ADJUDICATION_QUESTION,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    DEFAULT_PACKET_PATH,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    RELEASE_HOLD_TARGET,
    REVIEW_ID,
    SCHEMA_ID,
    SELECTED_TRANCHE_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_005_DEPENDENCY,
    TRANCHE_005_STATUS,
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_DEPENDENCY_CLASS,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004ReleaseReadinessAdjudicationPacketResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

PROHIBITED_POSITIVE_PHRASES = [
    "release packet assembled true",
    "v0.1-alpha marked ready",
    "Lean theorem debt discharged true",
    "proof debt reduced true",
    "retained assumptions discharged true",
    "Phase 2 authorized true",
    "seam closure authorized true",
    "empirical validation authorized true",
    "master action promoted",
    "claim promoted",
    "release packet ready",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_files_exist() -> None:
    assert DEFAULT_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert (
        review["consumes_packet"]
        == "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_v0"
    )
    assert review["consumes_packet_pointer"] == (
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_20260522_v0.json"
    )
    assert review["consumed_packet_schema_id"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_20260522_v0"
    )


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_accepts_question_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_scope"] == (
        "REVIEW_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_ONLY_"
        "AUTHORIZE_ADJUDICATION_EXECUTION_NO_RELEASE_DECISION"
    )
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert review["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert review["release_readiness_adjudication_question"] == ADJUDICATION_QUESTION
    assert review["retained_blocker_adjudication_question_accepted"] is True
    assert review["release_readiness_adjudication_execution_authorized"] is True
    assert review["release_readiness_adjudication_execution_scope"] == (
        "DECIDE_ONLY_WHETHER_V01_ALPHA_CAN_PROCEED_WITH_TRANCHE_004_RETAINED_OR_"
        "MUST_HOLD_RELEASE"
    )
    assert review["release_readiness_adjudication_executed"] is False
    assert review["release_readiness_question_answered"] is False
    assert review["release_readiness_decision_made"] is False
    assert review["release_readiness_proceed_authorized"] is False


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_preserves_queue_posture() -> None:
    review = _json(DEFAULT_OUT)
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == TRANCHE_003_STATUS
    assert review["tranche_005_status"] == TRANCHE_005_STATUS
    assert review["tranche_005_dependency"] == TRANCHE_005_DEPENDENCY
    assert review["tranche_006_status"] == TRANCHE_006_STATUS
    assert review["tranche_006_dependency"] == TRANCHE_006_DEPENDENCY
    assert review["tranche_006_dependency_class"] == TRANCHE_006_DEPENDENCY_CLASS
    assert review["tranche_006_dependency_finding_id"] == TRANCHE_006_FINDING_ID
    assert review["documented_dependency_nonblocking_tranche_count"] == 5
    assert [row["finding_id"] for row in review["documented_dependency_nonblocking_tranches"]] == [
        "V01-ALPHA-DEP-REM-001",
        "V01-ALPHA-DEP-REM-002",
        "V01-ALPHA-DEP-REM-003",
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    assert review["simple_dependency_remediation_queue_exhausted"] is True


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_keeps_tranche_004_retained() -> None:
    review = _json(DEFAULT_OUT)
    assert review["tranche_004_status"] == TRANCHE_004_STATUS
    retained = review["retained_tranche_004_carry_forward"]
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert review["release_readiness_blocked_by_tranche_004"] is True
    assert review["release_readiness_still_blocked"] is True
    assert review["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert review["tranche_004_status_downgraded"] is False
    assert review["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_forbidden_effects_false() -> None:
    review = _json(DEFAULT_OUT)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert review["release_hold_packet_prepared"] is False
    assert review["release_hold_registered"] is False
    assert review["release_packet_assembled"] is False
    assert review["v01_alpha_marked_ready"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced"] is False
    assert review["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert review["proof_debt_reduced"] is False
    assert review["retained_assumptions_discharged"] is False
    assert review["validation_claim_authorized"] is False

    combined = json.dumps(review, sort_keys=True) + "\n" + _read(ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_next_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "retained_tranche_004_release_readiness_adjudication_execution_only"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "EXECUTE_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_ONLY_NO_"
        "RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        RELEASE_HOLD_TARGET: "deferred",
        "assemble_v01_alpha_release_packet": "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_acceptance_and_determinism() -> None:
    review = _json(DEFAULT_OUT)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        packet_path=DEFAULT_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        packet_path=DEFAULT_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_20260522_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
        ADJUDICATION_QUESTION,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004ReleaseReadinessAdjudicationPacketResultReview" in index_text
    assert (
        "v01_retained_tranche_004_release_readiness_adjudication_packet_result_review_authorizes_execution_only"
        in index_text
    )
