from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    BLOCKED_OBJECT,
    DEFAULT_OUT as DEFAULT_PROGRAM_PATH,
    MISSING_OBJECT,
    OUTCOME_ID as PROGRAM_OUTCOME_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_FUTURE_ROUTE,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_005_DEPENDENCY,
    TRANCHE_005_STATUS,
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_DEPENDENCY_CLASS,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    REVIEW_ID,
    SCHEMA_ID,
    build_result_review,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_future_remediation_program_result_review_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004FutureRemediationProgramResultReview.lean"
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


def test_v01_alpha_retained_tranche_004_future_program_result_review_files_exist() -> None:
    assert DEFAULT_PROGRAM_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_future_program_result_review_consumes_program() -> None:
    review = _json(DEFAULT_OUT)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_future_remediation_program"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_v0"
    )
    assert review["consumes_future_remediation_program_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_20260522_v0.json"
    )
    program = _json(DEFAULT_PROGRAM_PATH)
    assert program["outcome_id"] == PROGRAM_OUTCOME_ID
    assert program["selected_next_target"] == (
        "review_v01_alpha_retained_tranche_004_future_remediation_program_result"
    )


def test_v01_alpha_retained_tranche_004_future_program_result_review_accepts_planning_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["future_remediation_program_reviewed"] is True
    assert review["future_remediation_program_accepted"] is True
    assert review["future_remediation_program_accepted_as_planning_only"] is True
    assert review["program_accepted_as_closure_evidence"] is False
    assert review["blocked_object"] == BLOCKED_OBJECT
    assert review["missing_object"] == MISSING_OBJECT
    assert len(review["evidence_required_before_revisiting_tranche_004"]) == 5
    assert len(review["proof_surfaces_required_before_status_movement"]) == 4
    assert len(review["documentation_alone_cannot_do"]) == 4
    assert len(review["failure_conditions"]) == 4
    assert len(review["success_conditions"]) == 3


def test_v01_alpha_retained_tranche_004_future_program_result_review_preserves_hold() -> None:
    review = _json(DEFAULT_OUT)
    assert review["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert review["release_readiness_held"] is True
    assert review["release_readiness_still_blocked"] is True
    assert review["release_readiness_blocked_by_tranche_004"] is True
    assert review["release_readiness_proceed_authorized"] is False
    assert review["release_assembly_authorized"] is False
    assert review["release_assembly_authorized_by_review"] is False
    assert review["release_packet_assembled"] is False
    assert review["v01_alpha_marked_ready"] is False


def test_v01_alpha_retained_tranche_004_future_program_result_review_preserves_queue() -> None:
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
    assert review["dependency_remediation_queue_exhausted"] is True


def test_v01_alpha_retained_tranche_004_future_program_result_review_keeps_tranche_004() -> None:
    review = _json(DEFAULT_OUT)
    assert review["tranche_004_status"] == TRANCHE_004_STATUS
    retained = review["retained_tranche_004_carry_forward"]
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert review["required_future_route_for_tranche_004"] == TRANCHE_004_FUTURE_ROUTE
    assert review["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert review["tranche_004_status_moved_by_review"] is False
    assert review["tranche_004_status_downgraded"] is False
    assert review["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_retained_tranche_004_future_program_result_review_selects_bounded_route() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "bounded_source_map_witness_chain_research_packet_preparation_only"
    )
    assert review["selection_count"] == 1
    assert review["bounded_source_map_witness_chain_research_packet_authorized_for_preparation"] is True
    assert review["bounded_source_map_witness_chain_research_packet_prepared"] is False
    assert review["source_map_witness_chain_research_packet_prepared"] is False
    assert review["source_map_research_executed_by_review"] is False
    assert review["witness_chain_research_started"] is False
    assert review["witness_chain_constructed"] is False
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "return_to_main_physics_target_selection_after_v01_alpha_release_hold": "deferred",
        "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_continuation_packet": (
            "superseded_by_selected_refinement"
        ),
        "prepare_release_hold_summary_and_pause_v01_alpha_assembly": "deferred",
        "assemble_v01_alpha_release_packet": "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_future_program_result_review_forbidden_effects() -> None:
    review = _json(DEFAULT_OUT)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert review["source_map_closure_achieved"] is False
    assert review["source_map_closure_claimed"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["qft_gr_seam_closure_claimed"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced"] is False
    assert review["proof_debt_reduced"] is False
    assert review["retained_assumptions_discharged"] is False
    assert review["phase2_authorized"] is False
    assert review["empirical_validation_authorized"] is False
    assert review["master_action_promotion_authorized"] is False

    combined = json.dumps(review, sort_keys=True) + "\n" + _read(ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_retained_tranche_004_future_program_result_review_determinism() -> None:
    review = _json(DEFAULT_OUT)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        program_path=DEFAULT_PROGRAM_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        program_path=DEFAULT_PROGRAM_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_retained_tranche_004_future_program_result_review_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_RESULT_REVIEW_20260522_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_future_remediation_program_result_review_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_future_remediation_program_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
        BLOCKED_OBJECT,
        MISSING_OBJECT,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004FutureRemediationProgramResultReview" in index_text
    assert (
        "v01_alpha_retained_tranche_004_future_remediation_program_result_review_selects_bounded_witness_chain_packet"
        in index_text
    )
