from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_summary_after_tranche_006_movement_report import (
    DEFAULT_CAPTURED_AT_UTC,
    OUTCOME_ID as SUMMARY_OUTCOME_ID,
    PACKET_ID as SUMMARY_PACKET_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_report import (
    ADJUDICATION_QUESTION,
    DEFAULT_OUT,
    DEFAULT_SUMMARY_PATH,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    SCHEMA_ID,
    build_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_report.py"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004ReleaseReadinessAdjudicationPacket.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_files_exist() -> None:
    assert DEFAULT_SUMMARY_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_consumes_summary() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert (
        packet["consumes_dependency_remediation_summary_after_tranche_006_movement"]
        == SUMMARY_PACKET_ID
    )
    assert (
        packet["consumes_dependency_remediation_summary_after_tranche_006_movement_pointer"]
        == "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_20260522_v0.json"
    )


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_preserves_dependency_queue_posture() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["packet_scope"] == (
        "PREPARE_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_ONLY_NO_"
        "RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
    )
    assert packet["packet_classification"] == (
        "retained_tranche_004_release_readiness_adjudication_question_prepared"
    )
    assert packet["documented_dependency_nonblocking_tranche_count"] == 5
    assert [row["finding_id"] for row in packet["documented_dependency_nonblocking_tranches"]] == [
        "V01-ALPHA-DEP-REM-001",
        "V01-ALPHA-DEP-REM-002",
        "V01-ALPHA-DEP-REM-003",
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    assert packet["tranche_004_status"] == "retained_release_blocking_source_map_blocker"
    assert packet["simple_dependency_remediation_queue_exhausted"] is True
    assert packet["release_readiness_blocked_by_tranche_004"] is True
    assert packet["release_readiness_still_blocked"] is True


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_prepares_question_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_tranche_id"] == "V01-ALPHA-DEP-REM-TRANCHE-004"
    assert packet["selected_remediation_finding_id"] == "V01-ALPHA-DEP-REM-004"
    assert (
        packet["selected_dependency"]
        == "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
    )
    assert packet["release_readiness_adjudication_question"] == ADJUDICATION_QUESTION
    assert packet["release_readiness_adjudication_packet_prepared"] is True
    assert packet["release_readiness_adjudication_executed"] is False
    assert packet["release_readiness_question_answered"] is False
    assert packet["release_hold_packet_prepared"] is False
    assert packet["release_hold_registered"] is False


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_forbidden_effects_false() -> None:
    packet = _json(DEFAULT_OUT)
    for key, value in packet["forbidden_effect_status"].items():
        assert value is False, f"Forbidden effect unexpectedly true: {key}"
    assert packet["release_packet_assembled"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert packet["tranche_004_status_downgraded"] is False
    assert packet["tranche_004_retained_blocker_discharged"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["validation_claim_authorized"] is False


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_next_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "retained_tranche_004_release_readiness_adjudication_packet_result_review_only"
    )
    assert packet["selection_count"] == 1
    decisions = {row["target"]: row["decision"] for row in packet["candidate_next_targets"]}
    assert decisions == {
        "review_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_result": "selected",
        "execute_v01_alpha_retained_tranche_004_release_readiness_adjudication": "deferred",
        "prepare_v01_alpha_release_hold_packet_due_to_retained_tranche_004_blocker": "deferred",
    }


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_acceptance_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_packet(summary_path=DEFAULT_SUMMARY_PATH, captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    generated_2 = build_packet(summary_path=DEFAULT_SUMMARY_PATH, captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_20260522_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
        ADJUDICATION_QUESTION,
        SUMMARY_OUTCOME_ID,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004ReleaseReadinessAdjudicationPacket" in index_text
    assert (
        "v01_retained_tranche_004_release_readiness_adjudication_packet_prepares_question_only"
        in index_text
    )
