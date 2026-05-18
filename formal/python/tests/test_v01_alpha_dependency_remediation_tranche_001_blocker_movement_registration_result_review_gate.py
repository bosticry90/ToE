from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
    EXPECTED_AXIOMS,
    NEXT_TARGET,
    OUTCOME_ID,
    POLICY_CLASSIFICATION,
    PREVIOUS_BLOCKER_STATUS,
    REGISTERED_BLOCKER_STATUS,
    REGISTERED_MOVEMENT,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SELECTED_DEPENDENCY,
    SELECTED_REMEDIATION_FINDING_ID,
    SELECTED_TRANCHE_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
REGISTRATION_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche001BlockerMovementRegistrationResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
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

OTHER_EXPECTED_IDS = [
    "V01-ALPHA-DEP-REM-002",
    "V01-ALPHA-DEP-REM-003",
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_files_exist() -> None:
    assert REGISTRATION_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_consumes_registration() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_20260515_v0"
    )
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_registration"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_v0"
    )
    assert review["consumes_registration_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_registered_true() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "REVIEW_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_RESULT_ONLY_ACCEPT_DOCUMENTED_NONBLOCKING_MOVEMENT_NO_RELEASE_PROMOTION"
    )
    assert review["registered"] is True
    assert review["blocker_movement_registered"] is True
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert review["selected_dependency"] == SELECTED_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_exact_movement() -> None:
    review = _json(RESULT_REVIEW_PATH)
    movement = review["registered_movement"]
    assert movement["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert movement["selected_dependency"] == SELECTED_DEPENDENCY
    assert movement["previous_status"] == PREVIOUS_BLOCKER_STATUS
    assert movement["registered_status"] == REGISTERED_BLOCKER_STATUS
    assert movement["registered_movement"] == REGISTERED_MOVEMENT
    assert movement["movement_scope"] == "tranche_001_only"
    assert movement["registered_by_this_execution"] is True
    assert movement["requires_result_review_for_formal_acceptance"] is False


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_preserves_evidence_policy_documentation_chain() -> None:
    review = _json(RESULT_REVIEW_PATH)
    evidence = review["accepted_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["project_axioms_used"] == []
    assert evidence["project_axiom_count"] == 0
    assert evidence["classification"] == "exact_dependency_evidence_produced_no_project_axioms_detected"
    assert review["policy_classification"] == POLICY_CLASSIFICATION
    assert (
        review["documentation_result_review_classification"]
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
    )
    assert review["documentation_accepted_only_as_documentation"] is True
    assert review["documentation_surface"]["exists"] is True
    assert review["documentation_surface"]["accepted_as_documentation"] is True


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_accepts_formal_movement_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["blocker_movement_registration_result_review_classification"] == (
        RESULT_REVIEW_CLASSIFICATION
    )
    assert review["tranche_001_formal_movement_accepted"] is True
    assert review["tranche_001_release_blocker_status"] == REGISTERED_BLOCKER_STATUS
    assert review["tranche_001_dependency_policy_remediation_satisfied"] is True
    assert review["tranche_001_cleared_for_global_release_readiness"] is False
    assert review["global_release_readiness_still_blocked"] is True
    assert review["release_blocking_obligation_count_after_review"] == 5


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_other_five_unmodified() -> None:
    review = _json(RESULT_REVIEW_PATH)
    other = review["other_release_blocking_obligations"]
    assert review["other_release_blocking_obligation_count"] == 5
    assert [row["dependency_finding_id"] for row in other] == OTHER_EXPECTED_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_executed_in_tranche_001"
        assert row["modified_by_tranche_001"] is False


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_forbidden_effects_false() -> None:
    review = _json(RESULT_REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert review["release_packet_assembled"] is False
    assert review["v01_alpha_marked_ready"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced"] is False
    assert review["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert review["proof_debt_reduced"] is False
    assert review["retained_assumptions_discharged"] is False
    assert review["validation_claim_authorized"] is False


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "next_remediation_tranche_selection_packet_preparation_only"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_NEXT_REMEDIATION_TRANCHE_SELECTION_PACKET_ONLY_NO_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_002": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_acceptance_and_determinism() -> None:
    review = _json(RESULT_REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        registration_path=REGISTRATION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        registration_path=REGISTRATION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche001BlockerMovementRegistrationResultReview" in index_text
    assert (
        "v01_dependency_remediation_tranche_001_blocker_movement_registration_result_review_does_not_promote_release"
        in index_text
    )
