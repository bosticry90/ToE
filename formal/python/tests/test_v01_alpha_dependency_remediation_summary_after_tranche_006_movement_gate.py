from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_summary_after_tranche_006_movement_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    SCHEMA_ID,
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
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
    build_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_20260522_v0.json"
)
PACKET_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_20260522_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_summary_after_tranche_006_movement_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationSummaryAfterTranche006Movement.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "release_readiness_pause_registered",
    "release_readiness_adjudication_prepared",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert PACKET_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_consumes_result_review() -> None:
    packet = _json(PACKET_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_tranche_006_movement_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_v0"
    )
    assert packet["consumes_tranche_006_movement_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_20260522_v0.json"
    )


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_preserves_statuses() -> None:
    packet = _json(PACKET_PATH)
    assert packet["packet_scope"] == (
        "PREPARE_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_ONLY_"
        "NO_RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
    )
    assert packet["dependency_remediation_summary_classification"] == (
        "dependency_remediation_queue_exhausted_tranche_004_retained_release_blocker"
    )
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_004_status"] == TRANCHE_004_STATUS
    assert packet["tranche_005_status"] == TRANCHE_005_STATUS
    assert packet["tranche_005_dependency"] == TRANCHE_005_DEPENDENCY
    assert packet["tranche_006_status"] == TRANCHE_006_STATUS
    assert packet["tranche_006_dependency"] == TRANCHE_006_DEPENDENCY
    assert packet["tranche_006_formal_movement_accepted"] is True
    assert packet["tranche_006_moved_or_cleared"] is True


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_carries_tranche_004() -> None:
    packet = _json(PACKET_PATH)
    retained = packet["retained_tranche_004_carry_forward"]
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert packet["release_readiness_blocked_by_tranche_004"] is True
    assert packet["release_readiness_still_blocked"] is True
    blockers = packet["retained_release_blocking_obligations"]
    assert packet["retained_release_blocking_obligation_count"] == 1
    assert [row["dependency_finding_id"] for row in blockers] == [TRANCHE_004_FINDING_ID]
    assert blockers[0]["status_carry_forward"] == TRANCHE_004_STATUS


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_confirms_queue_exhausted() -> None:
    packet = _json(PACKET_PATH)
    assert packet["simple_dependency_remediation_queue_exhausted"] is True
    assert packet["unresolved_simple_dependency_tranches"] == []
    assert packet["unresolved_simple_dependency_tranche_count"] == 0
    documented = packet["documented_dependency_nonblocking_tranches"]
    assert packet["documented_dependency_nonblocking_tranche_count"] == 5
    assert [row["finding_id"] for row in documented] == [
        "V01-ALPHA-DEP-REM-001",
        "V01-ALPHA-DEP-REM-002",
        "V01-ALPHA-DEP-REM-003",
        "V01-ALPHA-DEP-REM-005",
        TRANCHE_006_FINDING_ID,
    ]


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_does_not_authorize_release() -> None:
    packet = _json(PACKET_PATH)
    assert packet["release_assembly_authorized"] is False
    assert packet["release_packet_assembled"] is False
    assert packet["readiness_marking_authorized"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["required_next_decision"] == (
        "retained_tranche_004_release_readiness_adjudication_or_release_hold"
    )
    assert packet["preferred_next_decision_path"] == NEXT_TARGET


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_forbidden_effects_false() -> None:
    packet = _json(PACKET_PATH)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["validation_claim_authorized"] is False


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_next_target() -> None:
    packet = _json(PACKET_PATH)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "retained_tranche_004_release_readiness_adjudication_packet_preparation_only"
    )
    assert packet["selection_count"] == 1
    assert packet["next_action_scope"] == (
        "PREPARE_RETAINED_TRANCHE_004_RELEASE_READINESS_ADJUDICATION_PACKET_ONLY_"
        "NO_RELEASE_ASSEMBLY_OR_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        "prepare_v01_alpha_retained_tranche_004_release_readiness_adjudication_packet": "selected",
        "prepare_v01_alpha_release_hold_packet_due_to_retained_tranche_004_blocker": "deferred",
        "assemble_v01_alpha_release_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_acceptance_and_determinism() -> None:
    packet = _json(PACKET_PATH)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_SUMMARY_AFTER_TRANCHE_006_MOVEMENT_20260522_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_summary_after_tranche_006_movement_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_summary_after_tranche_006_movement_gate.py",
        OUTCOME_ID,
        TRANCHE_006_DEPENDENCY,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationSummaryAfterTranche006Movement" in index_text
    assert (
        "v01_dependency_remediation_summary_after_tranche_006_movement_carries_tranche_004"
        in index_text
    )
