from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_002_audit_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    EXPECTED_AXIOMS,
    LEAN_SOURCE,
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
    TRANCHE_CLASSIFICATION,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
AUDIT_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_002_audit_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche002AuditResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "remediation_closure_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "expert_re_review_executed",
    "release_policy_adjudication_executed",
    "release_policy_decision_made",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
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

RELEASE_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-002",
    "V01-ALPHA-DEP-REM-003",
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

OTHER_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-003",
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
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


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_files_exist() -> None:
    assert AUDIT_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_consumes_audit() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_audit"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_v0"
    assert review["consumes_audit_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_selected_dependency() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "REVIEW_TRANCHE_002_AUDIT_RESULT_ONLY_NO_REMEDIATION_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert review["selected_dependency"] == SELECTED_DEPENDENCY
    assert review["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    selected = review["selected_release_blocking_obligation"]
    assert selected["dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_preserves_audit_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    target = review["lean_audit_target"]
    assert target["lean_target"] == LEAN_TARGET
    assert target["lean_source"] == LEAN_SOURCE
    assert target["command"] == (
        "#print axioms ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero"
    )
    assert target["command_context"] == "lake env lean --stdin"
    assert target["exit_code"] == 0


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_preserves_exact_evidence() -> None:
    review = _json(RESULT_REVIEW_PATH)
    evidence = review["exact_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["exact_axioms_or_dependencies_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
    assert evidence["axiom_classification"] == [
        {"axiom": "propext", "classification": "standard_lean_axiom"},
        {"axiom": "Classical.choice", "classification": "standard_lean_axiom"},
        {"axiom": "Quot.sound", "classification": "standard_lean_axiom"},
    ]
    assert evidence["classification"] == (
        "exact_dependency_evidence_produced_no_project_axioms_detected"
    )
    assert "stationary_implies_operator_zero" in evidence["raw_output"]


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_classifies_conservatively() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["tranche_002_audit_result_classification"] == TRANCHE_CLASSIFICATION
    assert review["audit_evidence_accepted"] is True
    assert review["release_policy_adjudication_packet_preparation_authorized"] is True
    assert review["release_policy_adjudication_executed"] is False
    assert review["release_policy_decision_made"] is False
    assert review["tranche_002_release_blocker_status"] == (
        "still_blocking_pending_release_policy_adjudication_packet_preparation"
    )
    assert review["remediation_closure_authorized"] is False
    assert review["remediation_closure_executed"] is False
    assert TRANCHE_CLASSIFICATION in review["classification_options_considered"]


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_keeps_blockers_tracked() -> None:
    review = _json(RESULT_REVIEW_PATH)
    rows = review["release_blocking_obligations_carry_forward"]
    assert review["release_blocking_obligation_count"] == 5
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS

    other = review["other_release_blocking_obligations"]
    assert review["other_release_blocking_obligation_count"] == 4
    assert [row["dependency_finding_id"] for row in other] == OTHER_BLOCKER_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_002"
        assert row["remediation_execution_status"] == "not_executed_v0"
        assert row["modified_by_tranche_002"] is False


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_forbidden_effects_false() -> None:
    review = _json(RESULT_REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert review["broader_remediation_executed"] is False
    assert review["blocker_movement_authorized"] is False
    assert review["blocker_movement_registered"] is False
    assert review["blocker_fully_remediated"] is False
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


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "tranche_002_release_policy_adjudication_packet_preparation_only"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_TRANCHE_002_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_dependency_remediation_tranche_002_release_policy_adjudication_packet": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_002_release_policy_adjudication": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_acceptance_and_determinism() -> None:
    review = _json(RESULT_REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        audit_path=AUDIT_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        audit_path=AUDIT_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_002_audit_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_002_audit_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche002AuditResultReview" in index_text
    assert (
        "v01_dependency_remediation_tranche_002_audit_result_review_does_not_move_blocker"
        in index_text
    )
