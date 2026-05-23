from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    ADJUDICATION_QUESTION,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    DEFAULT_RESULT_REVIEW_PATH,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    RELEASE_HOLD_PACKET_TARGET,
    RELEASE_READINESS_DECISION,
    SCHEMA_ID,
    EXECUTION_ID,
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
    build_adjudication,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_release_readiness_adjudication_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_EXECUTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004ReleaseReadinessAdjudication.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

PROHIBITED_POSITIVE_PHRASES = [
    "release packet assembled true",
    "v0.1-alpha marked ready",
    "Lean theorem debt discharged true",
    "proof debt reduced true",
    "retained assumptions discharged true",
    "Phase 2 authorized true",
    "source map closure claimed true",
    "QFT-GR seam closure claimed true",
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


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_files_exist() -> None:
    assert DEFAULT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_EXECUTION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_consumes_result_review() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["schema_id"] == SCHEMA_ID
    assert execution["execution_id"] == EXECUTION_ID
    assert execution["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert execution["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert execution["executed"] is True
    assert execution["accepted"] is True
    assert execution["outcome_id"] == OUTCOME_ID
    assert execution["consumes_result_review"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_v0"
    )
    assert execution["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_RESULT_REVIEW_20260522_v0.json"
    )


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_executes_narrow_question() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["execution_scope"] == (
        "EXECUTE_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_ONLY_NO_"
        "RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
    )
    assert execution["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert execution["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert execution["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert execution["release_readiness_adjudication_question"] == ADJUDICATION_QUESTION
    assert execution["release_readiness_adjudication_executed"] is True
    assert execution["release_readiness_question_answered"] is True
    assert execution["release_readiness_decision_made"] is True
    assert execution["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert execution["release_readiness_held"] is True
    assert execution["release_readiness_hold_reason"] == "retained_tranche_004_source_map_blocker"
    assert execution["release_readiness_proceed_authorized"] is False


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_preserves_dependency_queue() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["tranche_001_status"] == TRANCHE_001_STATUS
    assert execution["tranche_002_status"] == TRANCHE_002_STATUS
    assert execution["tranche_003_status"] == TRANCHE_003_STATUS
    assert execution["tranche_005_status"] == TRANCHE_005_STATUS
    assert execution["tranche_005_dependency"] == TRANCHE_005_DEPENDENCY
    assert execution["tranche_006_status"] == TRANCHE_006_STATUS
    assert execution["tranche_006_dependency"] == TRANCHE_006_DEPENDENCY
    assert execution["tranche_006_dependency_class"] == TRANCHE_006_DEPENDENCY_CLASS
    assert execution["tranche_006_dependency_finding_id"] == TRANCHE_006_FINDING_ID
    assert execution["documented_dependency_nonblocking_tranche_count"] == 5
    assert [row["finding_id"] for row in execution["documented_dependency_nonblocking_tranches"]] == [
        "V01-ALPHA-DEP-REM-001",
        "V01-ALPHA-DEP-REM-002",
        "V01-ALPHA-DEP-REM-003",
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    assert execution["simple_dependency_remediation_queue_exhausted"] is True


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_keeps_tranche_004_retained() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["tranche_004_status"] == TRANCHE_004_STATUS
    retained = execution["retained_tranche_004_carry_forward"]
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert execution["release_readiness_still_blocked"] is True
    assert execution["release_readiness_blocked_by_tranche_004"] is True
    assert execution["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert execution["tranche_004_status_downgraded"] is False
    assert execution["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_forbidden_effects_false() -> None:
    execution = _json(DEFAULT_OUT)
    forbidden = execution["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert execution["release_hold_packet_prepared"] is False
    assert execution["release_hold_registered"] is False
    assert execution["release_packet_assembled"] is False
    assert execution["v01_alpha_marked_ready"] is False
    assert execution["source_map_closure_claimed"] is False
    assert execution["qft_gr_seam_closure_claimed"] is False
    assert execution["lean_theorem_debt_discharged"] is False
    assert execution["axiom_spec_backed_debt_reduced"] is False
    assert execution["proof_debt_reduced"] is False
    assert execution["retained_assumptions_discharged"] is False
    assert execution["validation_claim_authorized"] is False

    combined = json.dumps(execution, sort_keys=True) + "\n" + _read(ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_next_target() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == (
        "retained_tranche_004_release_readiness_adjudication_result_review_only"
    )
    assert execution["selection_count"] == 1
    assert execution["next_action_scope"] == (
        "REVIEW_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_ONLY_NO_"
        "RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in execution["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        RELEASE_HOLD_PACKET_TARGET: "deferred",
        "prepare_v01_alpha_retained_blocker_release_policy_exception_packet": "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_acceptance_and_determinism() -> None:
    execution = _json(DEFAULT_OUT)
    for key, value in execution["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_adjudication(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_adjudication(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert execution == generated_1


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        EXECUTION_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_20260522_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_release_readiness_adjudication_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_release_readiness_adjudication_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
        RELEASE_READINESS_DECISION,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_EXECUTION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004ReleaseReadinessAdjudication" in index_text
    assert (
        "v01_retained_tranche_004_release_readiness_adjudication_holds_readiness_due_to_tranche_004"
        in index_text
    )
