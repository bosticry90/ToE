from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    EXPECTED_AXIOMS,
    LEAN_AUDIT_COMMAND,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    POLICY_CLASSIFICATION,
    POLICY_QUESTION,
    PROJECT_AXIOMS_USED,
    RESULT_REVIEW_CLASSIFICATION,
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
ADJUDICATION_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_20260522_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_20260522_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche006ReleasePolicyAdjudicationResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "remediation_closure_executed",
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "documentation_packet_prepared",
    "documentation_execution_performed",
    "expert_re_review_executed",
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "blocker_movement_registered",
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


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_files_exist() -> None:
    assert ADJUDICATION_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_consumes_adjudication() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_adjudication"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_v0"
    )
    assert review["consumes_adjudication_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_20260522_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_preserves_selected_dependency() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "REVIEW_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_RESULT_ONLY_"
        "AUTHORIZE_DOCUMENTATION_PACKET_PREPARATION_NO_BLOCKER_MOVEMENT"
    )
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == TRANCHE_003_STATUS
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert review["selected_dependency"] == SELECTED_DEPENDENCY
    assert review["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert review["lean_audit_target"]["lean_target"] == LEAN_TARGET
    assert review["lean_audit_target"]["command"] == LEAN_AUDIT_COMMAND


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_preserves_policy_result_and_evidence() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["policy_question"] == POLICY_QUESTION
    assert review["policy_classification"] == POLICY_CLASSIFICATION
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["policy_adjudication_result_accepted"] is True
    assert review["policy_adjudication_executed_before_review"] is True
    assert review["policy_decision_made_before_review"] is True
    assert review["policy_decision_made_by_review"] is False
    assert review["policy_decision_changed_by_review"] is False

    evidence = review["accepted_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["exact_axioms_or_dependencies_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_or_mathlib_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
    assert evidence["project_local_axioms_present"] is False
    assert "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0" in evidence[
        "raw_output"
    ]

    decision = review["policy_decision_reviewed"]
    assert decision["classification"] == POLICY_CLASSIFICATION
    assert decision["standard_lean_axioms_reviewed"] == EXPECTED_AXIOMS
    assert decision["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert decision["project_axiom_count"] == 0


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_authorizes_documentation_packet_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["documentation_requirement_open"] is True
    assert review["documentation_packet_preparation_authorized"] is True
    assert review["documentation_packet_prepared"] is False
    assert review["documentation_prepared"] is False
    assert review["documentation_execution_performed"] is False
    assert review["tranche_006_policy_status"] == "policy_acceptable_documentation_required"
    assert review["tranche_006_release_blocker_status"] == (
        "still_blocking_pending_documentation_packet"
    )
    assert review["remediation_fully_satisfied"] is False
    assert review["blocker_movement_authorized"] is False
    assert review["blocker_movement_registered"] is False


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_carries_tranche_004_and_005() -> None:
    review = _json(RESULT_REVIEW_PATH)
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

    assert review["tranche_005_status"] == TRANCHE_005_STATUS
    assert review["tranche_005_dependency"] == TRANCHE_005_DEPENDENCY
    assert review["tranche_006_status"] == "policy_acceptable_with_documentation_requirement"
    tranche_006 = review["tranche_006_obligation_carry_forward"]
    assert tranche_006["dependency_finding_id"] == SELECTED_FINDING_ID
    assert tranche_006["dependency"] == SELECTED_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_keeps_blockers_tracked() -> None:
    review = _json(RESULT_REVIEW_PATH)
    rows = review["release_blocking_obligations_carry_forward"]
    assert review["release_blocking_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in rows] == [
        TRANCHE_004_FINDING_ID,
        SELECTED_FINDING_ID,
    ]
    assert rows[0]["status_carry_forward"] == TRANCHE_004_STATUS
    assert rows[1]["status_carry_forward"] == (
        "pending_result_review_policy_acceptable_with_documentation_requirement"
    )

    other = review["other_release_blocking_obligations"]
    assert review["other_release_blocking_obligation_count"] == 1
    assert [row["dependency_finding_id"] for row in other] == [
        TRANCHE_004_FINDING_ID,
    ]
    for row in other:
        assert row["modified_by_tranche_006_policy_adjudication"] is False


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_forbidden_effects_false() -> None:
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

    combined = json.dumps(review, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "documentation_packet_preparation_only"
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_TRANCHE_006_DOCUMENTATION_PACKET_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_dependency_remediation_tranche_006_documentation_packet": "selected",
        "prepare_v01_alpha_dependency_remediation_tranche_006_status_adjudication_packet": "deferred",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_RESULT_REVIEW_20260522_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche006ReleasePolicyAdjudicationResultReview" in index_text
    assert (
        "v01_dependency_remediation_tranche_006_release_policy_adjudication_result_review_does_not_promote_release"
        in index_text
    )
