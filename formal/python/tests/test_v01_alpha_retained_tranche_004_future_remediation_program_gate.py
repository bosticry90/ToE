from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_post_hold_routing_packet_due_to_retained_tranche_004_report import (
    OUTCOME_ID as POST_HOLD_ROUTING_OUTCOME_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    BLOCKED_OBJECT,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    DEFAULT_POST_HOLD_ROUTING_PACKET_PATH,
    FORBIDDEN_EFFECTS,
    MISSING_OBJECT,
    NEXT_TARGET,
    OUTCOME_ID,
    PROGRAM_ID,
    PROGRAM_QUESTION,
    SCHEMA_ID,
    SOURCE_MAP_WITNESS_CHAIN_TARGET,
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
    build_future_remediation_program,
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
    / "v01_alpha_retained_tranche_004_future_remediation_program_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PROGRAM_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004FutureRemediationProgram.lean"
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


def test_v01_alpha_retained_tranche_004_future_remediation_program_files_exist() -> None:
    assert DEFAULT_POST_HOLD_ROUTING_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PROGRAM_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_future_remediation_program_consumes_packet() -> None:
    program = _json(DEFAULT_OUT)
    assert program["schema_id"] == SCHEMA_ID
    assert program["program_id"] == PROGRAM_ID
    assert program["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert program["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert program["prepared"] is True
    assert program["accepted"] is True
    assert program["outcome_id"] == OUTCOME_ID
    assert program["consumes_post_hold_routing_packet"] == (
        "V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_v0"
    )
    assert program["consumes_post_hold_routing_packet_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_20260522_v0.json"
    )
    post_hold = _json(DEFAULT_POST_HOLD_ROUTING_PACKET_PATH)
    assert post_hold["outcome_id"] == POST_HOLD_ROUTING_OUTCOME_ID
    assert post_hold["selected_next_target"] == (
        "prepare_v01_alpha_retained_tranche_004_future_remediation_program"
    )


def test_v01_alpha_retained_tranche_004_future_remediation_program_preserves_hold() -> None:
    program = _json(DEFAULT_OUT)
    assert program["program_question"] == PROGRAM_QUESTION
    assert program["blocked_object"] == BLOCKED_OBJECT
    assert program["missing_object"] == MISSING_OBJECT
    assert program["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert program["release_readiness_held"] is True
    assert program["release_readiness_still_blocked"] is True
    assert program["release_readiness_blocked_by_tranche_004"] is True
    assert program["release_readiness_proceed_authorized"] is False
    assert program["current_release_posture"] == {
        "public_release_completion": "not_authorized",
        "reason": RELEASE_READINESS_DECISION,
        "release_assembly": "unauthorized",
        "release_packet": "not_assembled",
        "release_readiness": "held",
    }


def test_v01_alpha_retained_tranche_004_future_remediation_program_preserves_queue() -> None:
    program = _json(DEFAULT_OUT)
    assert program["tranche_001_status"] == TRANCHE_001_STATUS
    assert program["tranche_002_status"] == TRANCHE_002_STATUS
    assert program["tranche_003_status"] == TRANCHE_003_STATUS
    assert program["tranche_005_status"] == TRANCHE_005_STATUS
    assert program["tranche_005_dependency"] == TRANCHE_005_DEPENDENCY
    assert program["tranche_006_status"] == TRANCHE_006_STATUS
    assert program["tranche_006_dependency"] == TRANCHE_006_DEPENDENCY
    assert program["tranche_006_dependency_class"] == TRANCHE_006_DEPENDENCY_CLASS
    assert program["tranche_006_dependency_finding_id"] == TRANCHE_006_FINDING_ID
    assert program["documented_dependency_nonblocking_tranche_count"] == 5
    assert [row["finding_id"] for row in program["documented_dependency_nonblocking_tranches"]] == [
        "V01-ALPHA-DEP-REM-001",
        "V01-ALPHA-DEP-REM-002",
        "V01-ALPHA-DEP-REM-003",
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    assert program["simple_dependency_remediation_queue_exhausted"] is True
    assert program["dependency_remediation_queue_exhausted"] is True


def test_v01_alpha_retained_tranche_004_future_remediation_program_keeps_tranche_004() -> None:
    program = _json(DEFAULT_OUT)
    assert program["tranche_004_status"] == TRANCHE_004_STATUS
    retained = program["retained_tranche_004_carry_forward"]
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert program["required_future_route_for_tranche_004"] == TRANCHE_004_FUTURE_ROUTE
    assert program["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert program["tranche_004_status_downgraded"] is False
    assert program["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_retained_tranche_004_future_remediation_program_defines_program() -> None:
    program = _json(DEFAULT_OUT)
    assert program["future_remediation_program_prepared"] is True
    assert program["future_remediation_program_executed"] is False
    assert len(program["evidence_required_before_revisiting_tranche_004"]) == 5
    assert len(program["proof_surfaces_required_before_status_movement"]) == 4
    assert len(program["documentation_alone_cannot_do"]) == 4
    assert len(program["failure_conditions"]) == 4
    assert len(program["success_conditions"]) == 3
    assert program["lane_classification"] == {
        "computational_physics_execution_status": "not_opened",
        "current_packet_lane": "release_control_plane",
        "main_physics_target_selection_status": "deferred_until_program_result_review",
        "release_assembly_status": "not_authorized",
        "release_lane_status": (
            "held_until_tranche_004_has_governed_resolution_or_hold_continuation"
        ),
        "substantive_future_work_lane": "bounded_qft_gr_source_map_research_mode",
    }
    assert all(
        row["current_status"] != "satisfied"
        for row in program["evidence_required_before_revisiting_tranche_004"]
    )


def test_v01_alpha_retained_tranche_004_future_remediation_program_selects_review() -> None:
    program = _json(DEFAULT_OUT)
    assert program["selected_next_target"] == NEXT_TARGET
    assert program["selected_next_target_kind"] == "future_remediation_program_result_review_only"
    assert program["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in program["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        SOURCE_MAP_WITNESS_CHAIN_TARGET: "deferred",
        "return_to_main_physics_target_selection_after_release_hold": "deferred",
        "prepare_release_hold_summary_and_pause_v01_alpha_assembly": "deferred",
        "assemble_v01_alpha_release_packet": "not_authorized",
    }


def test_v01_alpha_retained_tranche_004_future_remediation_program_forbidden_effects() -> None:
    program = _json(DEFAULT_OUT)
    forbidden = program["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert program["release_packet_assembled"] is False
    assert program["v01_alpha_marked_ready"] is False
    assert program["source_map_closure_achieved"] is False
    assert program["source_map_closure_claimed"] is False
    assert program["qft_gr_seam_closed"] is False
    assert program["qft_gr_seam_closure_claimed"] is False
    assert program["lean_theorem_debt_discharged"] is False
    assert program["axiom_spec_backed_debt_reduced"] is False
    assert program["proof_debt_reduced"] is False
    assert program["retained_assumptions_discharged"] is False
    assert program["phase2_authorized"] is False
    assert program["empirical_validation_authorized"] is False
    assert program["master_action_promotion_authorized"] is False
    assert program["source_map_witness_chain_research_packet_prepared"] is False
    assert program["witness_chain_research_started"] is False
    assert program["witness_chain_constructed"] is False

    combined = json.dumps(program, sort_keys=True) + "\n" + _read(ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_retained_tranche_004_future_remediation_program_determinism() -> None:
    program = _json(DEFAULT_OUT)
    for key, value in program["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_future_remediation_program(
        post_hold_packet_path=DEFAULT_POST_HOLD_ROUTING_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_future_remediation_program(
        post_hold_packet_path=DEFAULT_POST_HOLD_ROUTING_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert program == generated_1


def test_v01_alpha_retained_tranche_004_future_remediation_program_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        PROGRAM_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_20260522_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_future_remediation_program_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_future_remediation_program_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
        BLOCKED_OBJECT,
        MISSING_OBJECT,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PROGRAM_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004FutureRemediationProgram" in index_text
    assert "v01_alpha_retained_tranche_004_future_remediation_program_selects_result_review" in index_text
