from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    EXPECTED_AXIOMS,
    EXPECTED_POLICY_QUESTION,
    FORBIDDEN_EFFECTS,
    LEAN_AUDIT_COMMAND,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    PROJECT_AXIOMS_USED,
    REVIEW_ID,
    SCHEMA_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
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
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
PACKET_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260522_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche006ReleasePolicyAdjudicationPacketResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

PROHIBITED_POSITIVE_PHRASES = [
    "release packet assembled true",
    "v0.1-alpha marked ready",
    "Lean theorem debt discharged true",
    "proof debt reduced true",
    "retained assumptions discharged true",
    "Phase 2 authorized true",
    "seam closure authorized true",
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


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_consumes_packet() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_packet"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_v0"
    )
    assert review["consumes_packet_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_20260515_v0.json"
    )
    assert review["source_audit_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_v0"
    )


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_preserves_selected_dependency() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "REVIEW_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_"
        "AUTHORIZE_POLICY_ADJUDICATION_EXECUTION_NO_POLICY_DECISION"
    )
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == TRANCHE_003_STATUS
    assert review["tranche_005_status"] == TRANCHE_005_STATUS
    assert review["tranche_005_dependency"] == TRANCHE_005_DEPENDENCY
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert review["selected_dependency"] == SELECTED_DEPENDENCY
    assert review["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_preserves_evidence() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["lean_audit_target"]["lean_target"] == LEAN_TARGET
    assert review["lean_audit_target"]["command"] == LEAN_AUDIT_COMMAND
    assert review["lean_audit_target"]["exit_code"] == 0

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
    assert SELECTED_DEPENDENCY in evidence["raw_output"]


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_accepts_policy_question_without_deciding() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["packet_preparation_accepted"] is True
    assert review["policy_question"] == EXPECTED_POLICY_QUESTION
    assert len(review["release_policy_acceptance_criteria"]) >= 6
    assert len(review["release_policy_failure_criteria"]) >= 6
    assert "standard Lean axiom posture of tranche 006" in review["expert_re_review_requirement"]
    assert review["policy_adjudication_execution_authorized"] is True
    assert review["policy_adjudication_execution_scope"] == (
        "DECIDE_ONLY_WHETHER_STANDARD_LEAN_AXIOMS_ARE_ACCEPTABLE_FOR_TRANCHE_006_"
        "UNDER_V01_ALPHA_POLICY_GIVEN_EMPTY_PROJECT_AXIOMS"
    )
    assert review["policy_decision_made"] is False
    assert review["policy_adjudication_executed"] is False


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_carries_tranche_004() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["tranche_004_status"] == TRANCHE_004_STATUS
    retained = review["retained_tranche_004_carry_forward"]
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert review["retained_tranche_004_release_blocker_carry_forward_required"] is True
    assert review["release_readiness_blocked_by_tranche_004"] is True
    assert review["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert review["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_keeps_blockers_tracked() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["tranche_006_release_blocker_status"] == (
        "still_blocking_pending_policy_adjudication_execution"
    )
    assert review["remediation_closure_authorized"] is False
    assert review["remediation_closure_executed"] is False
    assert review["remediation_fully_satisfied"] is False
    assert review["blocker_movement_authorized"] is False
    assert review["blocker_movement_registered"] is False
    assert review["tranche_006_moved_or_cleared"] is False

    rows = review["release_blocking_obligations_carry_forward"]
    assert review["release_blocking_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in rows] == [
        TRANCHE_004_FINDING_ID,
        SELECTED_FINDING_ID,
    ]
    assert rows[0]["status_carry_forward"] == TRANCHE_004_STATUS
    assert rows[1]["status_carry_forward"] == (
        "release_blocking_pending_tranche_006_policy_adjudication_execution"
    )

    other = review["other_release_blocking_obligations"]
    assert review["other_release_blocking_obligation_count"] == 1
    assert other[0]["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert other[0]["modified_by_tranche_006_release_policy_packet_result_review"] is False


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_forbidden_effects_false() -> None:
    review = _json(RESULT_REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert review["release_packet_assembled"] is False
    assert review["v01_alpha_marked_ready"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced"] is False
    assert review["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert review["proof_debt_reduced"] is False
    assert review["retained_assumptions_discharged"] is False
    assert review["validation_claim_authorized"] is False

    combined = json.dumps(review, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "policy_adjudication_execution_only"
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "EXECUTE_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_ONLY_NO_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "execute_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication": "selected",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred",
        "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_006": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260522_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert (
        "V01DependencyRemediationTranche006ReleasePolicyAdjudicationPacketResultReview"
        in index_text
    )
    assert (
        "v01_dependency_remediation_tranche_006_release_policy_adjudication_packet_result_review_does_not_make_policy_decision"
        in index_text
    )
