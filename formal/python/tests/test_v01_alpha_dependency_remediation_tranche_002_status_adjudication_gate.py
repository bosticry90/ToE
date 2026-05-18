from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_002_status_adjudication_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
    EXPECTED_AXIOMS,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    POLICY_CLASSIFICATION,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_REMEDIATION_FINDING_ID,
    SELECTED_TRANCHE_ID,
    STATUS_CLASSIFICATION,
    STATUS_DECISION,
    TRANCHE_001_STATUS,
    build_adjudication,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
ADJUDICATION_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_002_status_adjudication_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_ADJUDICATION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche002StatusAdjudication.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "blocker_fully_remediated",
    "blocker_movement_authorized",
    "blocker_movement_registered",
    "remediation_closure_executed",
    "broader_remediation_executed",
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

OTHER_EXPECTED_IDS = [
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


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert ADJUDICATION_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ADJUDICATION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_consumes_result_review() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_20260515_v0"
    )
    assert adjudication["execution_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_v0"
    )
    assert adjudication["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert adjudication["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert adjudication["executed"] is True
    assert adjudication["accepted"] is True
    assert adjudication["outcome_id"] == OUTCOME_ID
    assert adjudication["consumes_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW_v0"
    )
    assert adjudication["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_adjudicates_only_selected_dependency() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["execution_scope"] == (
        "EXECUTE_TRANCHE_002_STATUS_ADJUDICATION_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert adjudication["tranche_001_status"] == TRANCHE_001_STATUS
    assert adjudication["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert adjudication["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert adjudication["selected_dependency"] == SELECTED_DEPENDENCY
    assert adjudication["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert adjudication["lean_audit_target"]["lean_target"] == LEAN_TARGET

    decision = adjudication["status_adjudication_decision"]
    assert decision["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert decision["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert decision["selected_dependency"] == SELECTED_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_preserves_evidence() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    evidence = adjudication["accepted_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["exact_axioms_or_dependencies_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == []
    assert evidence["project_axiom_count"] == 0
    assert evidence["classification"] == "exact_dependency_evidence_produced_no_project_axioms_detected"
    assert "propext" in evidence["raw_output"]
    assert "Classical.choice" in evidence["raw_output"]
    assert "Quot.sound" in evidence["raw_output"]


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_preserves_policy_and_documentation_chain() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["policy_classification"] == POLICY_CLASSIFICATION
    assert (
        adjudication["documentation_result_review_classification"]
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
    )
    assert adjudication["documentation_accepted_only_as_documentation"] is True
    assert adjudication["documentation_surface"]["exists"] is True
    assert adjudication["documentation_surface"]["accepted_as_documentation"] is True


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_decides_narrow_status_question() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["status_adjudication_executed"] is True
    assert adjudication["status_decision_made"] is True
    assert adjudication["status_adjudication_classification"] == STATUS_CLASSIFICATION
    assert adjudication["tranche_002_status_candidate"] == STATUS_DECISION

    decision = adjudication["status_adjudication_decision"]
    assert decision["decision"] == STATUS_DECISION
    assert decision["classification"] == STATUS_CLASSIFICATION
    assert decision["basis"] == [
        "accepted Lean dependency evidence [propext, Classical.choice, Quot.sound]",
        "project_axioms_used = []",
        "policy_acceptable_with_documentation_requirement",
        "documentation accepted as documentation only",
        "tranche 001 status = documented_dependency_nonblocking",
    ]
    assert decision["formal_blocker_movement_requires_result_review"] is True


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_keeps_blocker_unmoved_pending_review() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["tranche_002_release_blocker_status"] == (
        "pending_result_review_documented_dependency_nonblocking_candidate"
    )
    assert adjudication["post_adjudication_result_review_required"] is True
    assert adjudication["remediation_fully_satisfied"] is False
    assert adjudication["blocker_movement_authorized"] is False
    assert adjudication["blocker_movement_registered"] is False

    decision = adjudication["status_adjudication_decision"]
    assert decision["does_not_clear_blocker_by_itself"] is True
    assert decision["does_not_register_blocker_movement"] is True
    assert decision["does_not_discharge_theorem_or_proof_debt"] is True
    assert decision["does_not_mark_release_readiness"] is True


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_remaining_blockers_tracked() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    rows = adjudication["release_blocking_obligations_carry_forward"]
    assert adjudication["release_blocking_obligation_count"] == 5
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS

    other = adjudication["other_release_blocking_obligations"]
    assert adjudication["other_release_blocking_obligation_count"] == 4
    assert [row["dependency_finding_id"] for row in other] == OTHER_EXPECTED_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_002"
        assert row["modified_by_tranche_002"] is False


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_forbidden_effects_false() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    forbidden = adjudication["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert adjudication["release_packet_assembled"] is False
    assert adjudication["v01_alpha_marked_ready"] is False
    assert adjudication["lean_theorem_debt_discharged"] is False
    assert adjudication["axiom_spec_backed_debt_reduced"] is False
    assert adjudication["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert adjudication["proof_debt_reduced"] is False
    assert adjudication["retained_assumptions_discharged"] is False
    assert adjudication["validation_claim_authorized"] is False


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_next_target() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["selected_next_target"] == NEXT_TARGET
    assert adjudication["selected_next_target_kind"] == "status_adjudication_result_review_only"
    assert adjudication["selection_count"] == 1
    assert adjudication["next_action_scope"] == (
        "REVIEW_TRANCHE_002_STATUS_ADJUDICATION_RESULT_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in adjudication["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_002_status_adjudication_result": "selected",
        "prepare_v01_alpha_dependency_remediation_tranche_002_blocker_movement_registration_packet": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_acceptance_and_determinism() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    for key, value in adjudication["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_adjudication(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_adjudication(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert adjudication == generated_1


def test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_v0",
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_STATUS_ADJUDICATION_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_002_status_adjudication_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_002_status_adjudication_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_ADJUDICATION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche002StatusAdjudication" in index_text
    assert (
        "v01_dependency_remediation_tranche_002_status_adjudication_does_not_register_blocker_movement"
        in index_text
    )
