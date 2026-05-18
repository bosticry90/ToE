from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
    EXPECTED_AXIOMS,
    NEXT_TARGET,
    OUTCOME_ID,
    POLICY_CLASSIFICATION,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SELECTED_DEPENDENCY,
    SELECTED_REMEDIATION_FINDING_ID,
    SELECTED_TRANCHE_ID,
    STATUS_CLASSIFICATION,
    STATUS_DECISION,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
ADJUDICATION_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche001StatusAdjudicationResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "blocker_movement_registration_packet_prepared",
    "blocker_movement_registered",
    "blocker_fully_remediated",
    "blocker_movement_authorized",
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


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_files_exist() -> None:
    assert ADJUDICATION_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_consumes_adjudication() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_20260515_v0"
    )
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_adjudication"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_v0"
    )
    assert review["consumes_adjudication_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_preserves_selected_dependency() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "REVIEW_TRANCHE_001_STATUS_ADJUDICATION_RESULT_ONLY_AUTHORIZE_BLOCKER_MOVEMENT_REGISTRATION_PACKET_PREPARATION_NO_DIRECT_MOVEMENT"
    )
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert review["selected_dependency"] == SELECTED_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_preserves_candidate() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["status_candidate_reviewed"] == STATUS_DECISION
    assert review["status_adjudication_classification"] == STATUS_CLASSIFICATION
    assert (
        review["status_adjudication_result_review_classification"]
        == RESULT_REVIEW_CLASSIFICATION
    )
    assert review["documented_nonblocking_status_candidate_accepted"] is True
    assert review["tranche_001_release_blocker_status"] == (
        "status_candidate_accepted_pending_blocker_movement_registration_packet"
    )


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_preserves_evidence_policy_and_documentation() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_authorizes_registration_preparation_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["blocker_movement_registration_packet_preparation_authorized"] is True
    assert review["blocker_movement_registration_packet_prepared"] is False
    assert review["blocker_movement_registered"] is False
    assert review["remediation_fully_satisfied"] is False
    assert review["blocker_movement_authorized"] is False


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_other_five_unmodified() -> None:
    review = _json(RESULT_REVIEW_PATH)
    other = review["other_release_blocking_obligations"]
    assert review["other_release_blocking_obligation_count"] == 5
    assert [row["dependency_finding_id"] for row in other] == OTHER_EXPECTED_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_executed_in_tranche_001"
        assert row["modified_by_tranche_001"] is False


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_forbidden_effects_false() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "blocker_movement_registration_packet_preparation_only"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_TRANCHE_001_BLOCKER_MOVEMENT_REGISTRATION_PACKET_ONLY_NO_DIRECT_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_dependency_remediation_tranche_001_blocker_movement_registration_packet": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_002": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_acceptance_and_determinism() -> None:
    review = _json(RESULT_REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        adjudication_path=ADJUDICATION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        adjudication_path=ADJUDICATION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_STATUS_ADJUDICATION_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_001_status_adjudication_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche001StatusAdjudicationResultReview" in index_text
    assert (
        "v01_dependency_remediation_tranche_001_status_adjudication_result_review_does_not_move_blocker"
        in index_text
    )
