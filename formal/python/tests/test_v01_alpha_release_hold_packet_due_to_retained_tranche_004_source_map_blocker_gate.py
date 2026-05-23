from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    DEFAULT_RESULT_REVIEW_PATH,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    SCHEMA_ID,
    TRANCHE_004_FUTURE_ROUTE,
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
    build_hold_packet,
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
    / "v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01ReleaseHoldPacketDueToRetainedTranche004SourceMapBlocker.lean"
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


def test_v01_alpha_release_hold_packet_files_exist() -> None:
    assert DEFAULT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_release_hold_packet_consumes_result_review() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_result_review"] == (
        "V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_v0"
    )
    assert packet["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_RESULT_REVIEW_20260522_v0.json"
    )


def test_v01_alpha_release_hold_packet_records_hold_posture() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["dependency_remediation_queue_exhausted"] is True
    assert packet["release_hold_packet_prepared"] is True
    assert packet["release_hold_reason"] == "retained_tranche_004_source_map_blocker"
    assert packet["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert packet["release_readiness_held"] is True
    assert packet["release_readiness_still_blocked"] is True
    assert packet["release_readiness_blocked_by_tranche_004"] is True
    assert packet["release_readiness_proceed_authorized"] is False
    assert packet["release_hold_registered"] is False


def test_v01_alpha_release_hold_packet_preserves_dependency_queue() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_005_status"] == TRANCHE_005_STATUS
    assert packet["tranche_005_dependency"] == TRANCHE_005_DEPENDENCY
    assert packet["tranche_006_status"] == TRANCHE_006_STATUS
    assert packet["tranche_006_dependency"] == TRANCHE_006_DEPENDENCY
    assert packet["tranche_006_dependency_class"] == TRANCHE_006_DEPENDENCY_CLASS
    assert packet["tranche_006_dependency_finding_id"] == TRANCHE_006_FINDING_ID
    assert packet["documented_dependency_nonblocking_tranche_count"] == 5
    assert [row["finding_id"] for row in packet["documented_dependency_nonblocking_tranches"]] == [
        "V01-ALPHA-DEP-REM-001",
        "V01-ALPHA-DEP-REM-002",
        "V01-ALPHA-DEP-REM-003",
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    assert packet["simple_dependency_remediation_queue_exhausted"] is True


def test_v01_alpha_release_hold_packet_keeps_tranche_004_retained() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["tranche_004_status"] == TRANCHE_004_STATUS
    retained = packet["retained_tranche_004_carry_forward"]
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert packet["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert packet["tranche_004_status_downgraded"] is False
    assert packet["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_release_hold_packet_records_required_future_route() -> None:
    packet = _json(DEFAULT_OUT)
    route = packet["tranche_004_future_route_required"]
    assert packet["required_future_route_for_tranche_004"] == TRANCHE_004_FUTURE_ROUTE
    assert route["route_id"] == TRANCHE_004_FUTURE_ROUTE
    assert route["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert route["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert route["required_before_release_assembly"] is True
    assert route["not_satisfied_by_this_packet"] is True
    assert (
        route["continuation_target_candidate"]
        == "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_continuation_packet"
    )


def test_v01_alpha_release_hold_packet_forbidden_effects_false() -> None:
    packet = _json(DEFAULT_OUT)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert packet["release_packet_assembled"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["source_map_closure_achieved"] is False
    assert packet["source_map_closure_claimed"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["qft_gr_seam_closure_claimed"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["phase2_authorized"] is False
    assert packet["empirical_validation_authorized"] is False
    assert packet["master_action_promotion_authorized"] is False

    combined = json.dumps(packet, sort_keys=True) + "\n" + _read(ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_release_hold_packet_next_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == "release_hold_packet_result_review_only"
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_continuation_packet": "deferred",
        "assemble_v01_alpha_release_packet": "not_authorized",
    }


def test_v01_alpha_release_hold_packet_acceptance_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_hold_packet(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_hold_packet(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_release_hold_packet_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_RELEASE_HOLD_PACKET_DUE_TO_RETAINED_TRANCHE_004_SOURCE_MAP_BLOCKER_20260522_v0.json",
        "formal/python/tools/v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker_report.py",
        "formal/python/tests/test_v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
        RELEASE_READINESS_DECISION,
        TRANCHE_004_FUTURE_ROUTE,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01ReleaseHoldPacketDueToRetainedTranche004SourceMapBlocker" in index_text
    assert (
        "v01_alpha_release_hold_packet_due_to_retained_tranche_004_records_hold"
        in index_text
    )
