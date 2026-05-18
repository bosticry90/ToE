from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_report import (
    CANDIDATE_BLOCKER_STATUS,
    CURRENT_BLOCKER_STATUS,
    DEFAULT_CAPTURED_AT_UTC,
    DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
    EXPECTED_AXIOMS,
    LEAN_AUDIT_COMMAND,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    POLICY_CLASSIFICATION,
    PROJECT_AXIOMS_USED,
    PROPOSED_MOVEMENT,
    PROPOSED_MOVEMENT_TOKEN,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    STATUS_CANDIDATE,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
PACKET_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche005BlockerMovementRegistrationPacketResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "blocker_movement_registered",
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_reclassified_nonblocking",
    "tranche_004_retained_blocker_discharged",
    "remediation_closure_executed",
    "remediation_executed",
    "broader_remediation_executed",
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


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_consumes_packet() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW_20260515_v0"
    )
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_packet"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_v0"
    )
    assert review["consumes_packet_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_preserves_selected_dependency() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "REVIEW_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_ONLY_"
        "AUTHORIZE_REGISTRATION_EXECUTION_NO_LIVE_BLOCKER_MOVEMENT"
    )
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert review["selected_dependency"] == SELECTED_DEPENDENCY
    assert review["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert review["lean_audit_target"]["lean_target"] == LEAN_TARGET
    assert review["lean_audit_target"]["command"] == LEAN_AUDIT_COMMAND


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_accepts_exact_proposed_movement() -> None:
    review = _json(RESULT_REVIEW_PATH)
    proposal = review["movement_proposal"]
    assert review["status_candidate_reviewed"] == STATUS_CANDIDATE
    assert review["proposed_movement_accepted"] is True
    assert proposal["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert proposal["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert proposal["selected_dependency"] == SELECTED_DEPENDENCY
    assert proposal["current_status"] == CURRENT_BLOCKER_STATUS
    assert proposal["candidate_status"] == CANDIDATE_BLOCKER_STATUS
    assert proposal["accepted_status_candidate"] == STATUS_CANDIDATE
    assert proposal["proposed_movement"] == PROPOSED_MOVEMENT
    assert proposal["proposed_movement_token"] == PROPOSED_MOVEMENT_TOKEN
    assert proposal["movement_scope"] == "tranche_005_only"
    assert proposal["tranche_001_status"] == TRANCHE_001_STATUS
    assert proposal["tranche_002_status"] == TRANCHE_002_STATUS
    assert proposal["tranche_003_status"] == TRANCHE_003_STATUS
    assert proposal["tranche_004_status"] == TRANCHE_004_STATUS
    assert proposal["tranche_006_status"] == TRANCHE_006_STATUS


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_preserves_evidence_policy_and_documentation() -> None:
    review = _json(RESULT_REVIEW_PATH)
    evidence = review["accepted_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["exact_axioms_or_dependencies_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_or_mathlib_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
    assert evidence["project_local_axioms_present"] is False
    assert evidence["classification"] == "exact_dependency_evidence_produced_no_project_axioms_detected"
    assert review["policy_classification"] == POLICY_CLASSIFICATION
    assert (
        review["documentation_result_review_classification"]
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
    )
    assert review["documentation_accepted_only_as_documentation"] is True
    assert review["documentation_surface"]["exists"] is True
    assert review["documentation_surface"]["accepted_as_documentation"] is True


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_authorizes_execution_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    proposal = review["movement_proposal"]
    assert (
        review["blocker_movement_registration_packet_result_review_classification"]
        == RESULT_REVIEW_CLASSIFICATION
    )
    assert review["blocker_movement_registration_packet_prepared"] is True
    assert review["blocker_movement_registration_execution_authorized"] is True
    assert review["blocker_movement_registered"] is False
    assert review["blocker_movement_authorized"] is False
    assert review["remediation_fully_satisfied"] is False
    assert proposal["registers_movement_now"] is False
    assert proposal["clears_blocker_now"] is False
    assert proposal["marks_release_readiness_now"] is False


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_carries_posture() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == TRANCHE_003_STATUS
    assert review["tranche_004_status"] == TRANCHE_004_STATUS

    retained = review["retained_tranche_004_carry_forward"]
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert review["release_readiness_blocked_by_tranche_004"] is True
    assert review["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert review["tranche_004_retained_blocker_discharged"] is False

    assert review["tranche_006_status"] == TRANCHE_006_STATUS
    tranche_006 = review["tranche_006_obligation_carry_forward"]
    assert tranche_006["dependency_finding_id"] == TRANCHE_006_FINDING_ID
    assert tranche_006["dependency"] == TRANCHE_006_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_remaining_blockers_tracked() -> None:
    review = _json(RESULT_REVIEW_PATH)
    rows = review["release_blocking_obligations_carry_forward"]
    assert review["release_blocking_obligation_count"] == 3
    assert [row["dependency_finding_id"] for row in rows] == [
        TRANCHE_004_FINDING_ID,
        SELECTED_FINDING_ID,
        TRANCHE_006_FINDING_ID,
    ]
    assert rows[0]["status_carry_forward"] == TRANCHE_004_STATUS
    assert rows[1]["status_carry_forward"] == (
        "pending_result_review_policy_acceptable_with_documentation_requirement"
    )
    assert rows[2]["status_carry_forward"] == TRANCHE_006_STATUS

    other = review["other_release_blocking_obligations"]
    assert review["other_release_blocking_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in other] == [
        TRANCHE_004_FINDING_ID,
        TRANCHE_006_FINDING_ID,
    ]
    for row in other:
        assert row["modified_by_tranche_005_policy_adjudication"] is False


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_forbidden_effects_false() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "blocker_movement_registration_execution_only"
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "EXECUTE_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_ONLY_NO_RELEASE_PROMOTION_OR_GLOBAL_DEBT_DISCHARGE"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "execute_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration": "selected",
        "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_005_movement": "deferred",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert (
        "V01DependencyRemediationTranche005BlockerMovementRegistrationPacketResultReview"
        in index_text
    )
    assert (
        "v01_dependency_remediation_tranche_005_blocker_movement_registration_packet_result_review_does_not_register_movement"
        in index_text
    )
