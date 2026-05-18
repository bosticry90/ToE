from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_report import (
    CONSTRUCTION_ATTEMPT_CLASSIFICATION,
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    RETAINED_BLOCKER_REASON,
    SCHEMA_ID,
    SELECTED_NEXT_DEPENDENCY,
    SELECTED_NEXT_DEPENDENCY_CLASS,
    SELECTED_NEXT_FINDING_ID,
    SELECTED_NEXT_TRANCHE_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_STATUS,
    UNRESOLVED_NON_TRANCHE_004_IDS,
    build_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_20260515_v0.json"
)
PACKET_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_DECLARATION_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationNextTrancheSelectionPacketAfterTranche004RetainedBlockerDeclaration.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "remediation_execution_authorized",
    "remediation_executed",
    "selected_tranche_execution_packet_prepared",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_reclassified_nonblocking",
    "tranche_004_retained_blocker_discharged",
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

ALL_RELEASE_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert PACKET_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_consumes_result_review() -> None:
    packet = _json(PACKET_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_retained_blocker_declaration_result_review"] == (
        "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_v0"
    )
    assert packet["consumes_retained_blocker_declaration_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_preserves_statuses() -> None:
    packet = _json(PACKET_PATH)
    assert packet["packet_scope"] == (
        "PREPARE_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_"
        "DECLARATION_ONLY_NO_REMEDIATION_EXECUTION_RELEASE_PROMOTION_OR_READINESS_MARKING"
    )
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_004_status"] == TRANCHE_004_STATUS
    assert packet["release_readiness_blocked_by_tranche_004"] is True
    assert packet["release_readiness_still_blocked"] is True


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_carries_tranche_004() -> None:
    packet = _json(PACKET_PATH)
    retained = packet["retained_tranche_004_carry_forward"]
    assert retained["tranche_id"] == "V01-ALPHA-DEP-REM-TRANCHE-004"
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == RETAINED_BLOCKER_REASON
    assert retained["construction_attempt_classification"] == CONSTRUCTION_ATTEMPT_CLASSIFICATION
    assert retained["release_readiness_blocked_by_tranche_004"] is True
    assert retained["moved_to_documented_dependency_nonblocking"] is False
    assert packet["retained_tranche_004_release_blocker_carry_forward_required"] is True
    assert packet["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert packet["tranche_004_reclassified_nonblocking"] is False
    assert packet["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_tracks_current_ledger() -> None:
    packet = _json(PACKET_PATH)
    rows = packet["release_blocking_obligations_carry_forward"]
    assert packet["release_blocking_obligation_count"] == 3
    assert [row["dependency_finding_id"] for row in rows] == ALL_RELEASE_BLOCKER_IDS
    for row in rows:
        assert row["modified_by_tranche_003"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_003"

    unresolved = packet["unresolved_non_tranche_004_obligations"]
    assert packet["unresolved_non_tranche_004_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in unresolved] == UNRESOLVED_NON_TRANCHE_004_IDS
    for row in unresolved:
        assert row["modified_by_tranche_004"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_004"


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_selects_tranche_005() -> None:
    packet = _json(PACKET_PATH)
    selected = packet["selected_next_remediation_tranche"]
    assert packet["selection_count"] == 1
    assert packet["selected_next_tranche_id"] == SELECTED_NEXT_TRANCHE_ID
    assert packet["selected_next_dependency_finding_id"] == SELECTED_NEXT_FINDING_ID
    assert packet["selected_next_dependency"] == SELECTED_NEXT_DEPENDENCY
    assert packet["selected_next_dependency_class"] == SELECTED_NEXT_DEPENDENCY_CLASS
    assert selected["selected_tranche_id"] == SELECTED_NEXT_TRANCHE_ID
    assert selected["selected_dependency_finding_id"] == SELECTED_NEXT_FINDING_ID
    assert selected["selected_dependency"] == SELECTED_NEXT_DEPENDENCY
    assert selected["selected_dependency_class"] == SELECTED_NEXT_DEPENDENCY_CLASS
    assert selected["selection_method"] == "stable_order_first_unresolved_non_tranche_004_obligation"
    assert packet["selection_policy"]["eligible_finding_ids"] == UNRESOLVED_NON_TRANCHE_004_IDS
    assert packet["selection_policy"]["selected_finding_id"] == SELECTED_NEXT_FINDING_ID
    assert packet["selection_policy"]["retained_tranche_004_excluded_from_next_selection"] is True
    assert packet["selection_policy"]["retained_tranche_004_carried_forward"] is True


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_prepares_selection_only() -> None:
    packet = _json(PACKET_PATH)
    selected = packet["selected_next_remediation_tranche"]
    assert selected["execution_prepared"] is False
    assert selected["execution_authorized"] is False
    assert selected["remediation_executed"] is False
    assert selected["requires_result_review_before_execution_packet"] is True
    assert packet["remediation_execution_authorized"] is False
    assert packet["remediation_executed"] is False
    assert packet["selected_tranche_execution_packet_prepared"] is False
    assert packet["release_readiness_pause_registered"] is False
    assert packet["release_readiness_adjudication_prepared"] is False


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_forbidden_effects_false() -> None:
    packet = _json(PACKET_PATH)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert packet["blocker_movement_authorized"] is False
    assert packet["blocker_movement_registered"] is False
    assert packet["blocker_fully_remediated"] is False
    assert packet["release_packet_assembled"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["validation_claim_authorized"] is False


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_next_target() -> None:
    packet = _json(PACKET_PATH)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "next_tranche_selection_after_tranche_004_retained_blocker_result_review_only"
    )
    assert packet["next_action_scope"] == (
        "REVIEW_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_"
        "DECLARATION_ONLY_NO_REMEDIATION_EXECUTION_RELEASE_PROMOTION_OR_READINESS_MARKING"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_result": "selected",
        "prepare_v01_alpha_dependency_remediation_tranche_005_execution_packet": "deferred",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred",
    }


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_DECLARATION_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_gate.py",
        OUTCOME_ID,
        SELECTED_NEXT_DEPENDENCY,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert (
        "V01DependencyRemediationNextTrancheSelectionPacketAfterTranche004RetainedBlockerDeclaration"
        in index_text
    )
    assert (
        "v01_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_selects_tranche_005"
        in index_text
    )
