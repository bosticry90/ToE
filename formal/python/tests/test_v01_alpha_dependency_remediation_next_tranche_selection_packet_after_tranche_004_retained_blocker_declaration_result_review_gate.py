from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    RETAINED_BLOCKER_REASON,
    REVIEW_ID,
    SCHEMA_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    SELECTION_METHOD,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_STATUS,
    UNRESOLVED_NON_TRANCHE_004_IDS,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
PACKET_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_DECLARATION_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_DECLARATION_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationNextTrancheSelectionPacketAfterTranche004RetainedBlockerDeclarationResultReview.lean"
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


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_consumes_packet() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["logical_review_target"] == (
        "review_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_result"
    )
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_next_tranche_selection_packet"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_DECLARATION_v0"
    )
    assert review["consumes_next_tranche_selection_packet_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_DECLARATION_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_preserves_statuses() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "REVIEW_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_"
        "DECLARATION_ONLY_ACCEPT_TRANCHE_005_SELECTION_NO_REMEDIATION_EXECUTION_"
        "OR_RELEASE_PROMOTION"
    )
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == TRANCHE_003_STATUS
    assert review["tranche_004_status"] == TRANCHE_004_STATUS
    assert review["release_readiness_blocked_by_tranche_004"] is True
    assert review["release_readiness_still_blocked"] is True


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_carries_tranche_004() -> None:
    review = _json(RESULT_REVIEW_PATH)
    retained = review["retained_tranche_004_carry_forward"]
    assert retained["tranche_id"] == "V01-ALPHA-DEP-REM-TRANCHE-004"
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == RETAINED_BLOCKER_REASON
    assert retained["moved_to_documented_dependency_nonblocking"] is False
    assert review["retained_tranche_004_release_blocker_carry_forward_required"] is True
    assert review["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert review["tranche_004_reclassified_nonblocking"] is False
    assert review["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_tracks_current_ledger() -> None:
    review = _json(RESULT_REVIEW_PATH)
    rows = review["release_blocking_obligations_carry_forward"]
    assert review["release_blocking_obligation_count"] == 3
    assert [row["dependency_finding_id"] for row in rows] == ALL_RELEASE_BLOCKER_IDS
    for row in rows:
        assert row["modified_by_tranche_003"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_003"

    unresolved = review["unresolved_non_tranche_004_obligations"]
    assert review["unresolved_non_tranche_004_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in unresolved] == UNRESOLVED_NON_TRANCHE_004_IDS
    for row in unresolved:
        assert row["modified_by_tranche_004"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_004"


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_accepts_tranche_005_selection() -> None:
    review = _json(RESULT_REVIEW_PATH)
    selected = review["selected_next_remediation_tranche"]
    assert review["selection_count"] == 1
    assert review["selected_next_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_next_dependency_finding_id"] == SELECTED_FINDING_ID
    assert review["selected_next_dependency"] == SELECTED_DEPENDENCY
    assert review["selected_next_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert review["selection_method"] == SELECTION_METHOD
    assert selected["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert selected["selected_dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["selected_dependency"] == SELECTED_DEPENDENCY
    assert selected["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert selected["selection_method"] == SELECTION_METHOD
    assert review["tranche_005_selection_accepted"] is True


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_authorizes_preparation_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    selected = review["selected_next_remediation_tranche"]
    assert review["selection_result_review_classification"] == (
        "tranche_005_selection_accepted_execution_packet_preparation_pending"
    )
    assert review["tranche_005_execution_packet_preparation_authorized"] is True
    assert selected["requires_execution_packet_before_remediation"] is True
    assert selected["execution_prepared"] is False
    assert selected["execution_authorized"] is False
    assert selected["remediation_executed"] is False
    assert review["selected_tranche_execution_packet_prepared"] is False
    assert review["remediation_execution_authorized"] is False
    assert review["remediation_executed"] is False


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_forbidden_effects_false() -> None:
    review = _json(RESULT_REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert review["blocker_movement_authorized"] is False
    assert review["blocker_movement_registered"] is False
    assert review["blocker_fully_remediated"] is False
    assert review["release_packet_assembled"] is False
    assert review["v01_alpha_marked_ready"] is False
    assert review["release_readiness_pause_registered"] is False
    assert review["release_readiness_adjudication_prepared"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced"] is False
    assert review["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert review["proof_debt_reduced"] is False
    assert review["retained_assumptions_discharged"] is False
    assert review["validation_claim_authorized"] is False


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "tranche_005_execution_packet_preparation_only"
    )
    assert review["next_action_scope"] == (
        "PREPARE_TRANCHE_005_EXECUTION_PACKET_ONLY_NO_REMEDIATION_EXECUTION_"
        "OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_dependency_remediation_tranche_005_execution_packet": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_005": "deferred",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred",
    }


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_acceptance_and_determinism() -> None:
    review = _json(RESULT_REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_dependency_remediation_next_tranche_selection_after_tranche_004_retained_blocker_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_DECLARATION_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration_result_review_gate.py",
        OUTCOME_ID,
        SELECTED_DEPENDENCY,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert (
        "V01DependencyRemediationNextTrancheSelectionPacketAfterTranche004RetainedBlockerDeclarationResultReview"
        in index_text
    )
    assert (
        "v01_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_result_review_accepts_tranche_005_selection"
        in index_text
    )
