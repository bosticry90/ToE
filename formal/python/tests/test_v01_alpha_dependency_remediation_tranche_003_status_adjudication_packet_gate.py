from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
    EXPECTED_AXIOMS,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    POLICY_CLASSIFICATION,
    PROJECT_AXIOMS_USED,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_REMEDIATION_FINDING_ID,
    SELECTED_TRANCHE_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    build_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
PACKET_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche003StatusAdjudicationPacket.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "status_adjudication_executed",
    "status_decision_made",
    "blocker_status_adjudicated",
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
    "V01-ALPHA-DEP-REM-003",
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

OTHER_EXPECTED_IDS = [
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert PACKET_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_consumes_result_review() -> None:
    packet = _json(PACKET_PATH)
    assert packet["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_20260515_v0"
    )
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_documentation_packet_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_PACKET_RESULT_REVIEW_v0"
    )
    assert packet["consumes_documentation_packet_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_DOCUMENTATION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_preserves_selected_dependency() -> None:
    packet = _json(PACKET_PATH)
    assert packet["packet_scope"] == (
        "PREPARE_TRANCHE_003_STATUS_ADJUDICATION_PACKET_ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert packet["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert packet["selected_dependency"] == SELECTED_DEPENDENCY
    assert packet["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert packet["lean_audit_target"]["lean_target"] == LEAN_TARGET


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_preserves_evidence_policy_and_documentation() -> None:
    packet = _json(PACKET_PATH)
    evidence = packet["accepted_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["exact_axioms_or_dependencies_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_or_mathlib_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
    assert evidence["project_local_axioms_present"] is False
    assert evidence["classification"] == "exact_dependency_evidence_produced_no_project_axioms_detected"
    assert packet["policy_classification"] == POLICY_CLASSIFICATION
    assert (
        packet["documentation_result_review_classification"]
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
    )
    assert packet["documentation_accepted_only_as_documentation"] is True
    assert packet["documentation_surface"]["exists"] is True
    assert packet["documentation_surface"]["accepted_as_documentation"] is True


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_defines_question_only() -> None:
    packet = _json(PACKET_PATH)
    assert packet["status_adjudication_packet_prepared"] is True
    assert packet["status_adjudication_executed"] is False
    assert packet["status_decision_made"] is False
    assert packet["blocker_status_adjudicated"] is False
    assert packet["status_adjudication_question"] == (
        "Given accepted Lean dependency evidence, no project axioms, accepted release-policy posture, "
        "and accepted documentation, can tranche 003 move from release-blocking to a "
        "documented/narrower dependency status?"
    )
    assert packet["status_adjudication_inputs"] == [
        "accepted Lean dependency evidence [propext, Classical.choice, Quot.sound]",
        "project_axioms_used = []",
        "policy_acceptable_with_documentation_requirement",
        "documentation accepted as documentation only",
        "tranche 001 status = documented_dependency_nonblocking",
        "tranche 002 status = documented_dependency_nonblocking",
        "remaining release-blocking obligations tracked and unchanged",
    ]
    assert packet["candidate_status_outcomes"] == [
        "documented_dependency_nonblocking_pending_result_review",
        "documentation_accepted_but_recheck_required",
        "retained_blocker_pending_additional_evidence",
        "status_adjudication_failed_requires_redesign",
    ]


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_keeps_blocker_unmoved() -> None:
    packet = _json(PACKET_PATH)
    assert packet["tranche_003_release_blocker_status"] == (
        "still_blocking_pending_status_adjudication_packet_result_review"
    )
    assert packet["remediation_fully_satisfied"] is False
    assert packet["blocker_movement_authorized"] is False
    assert packet["blocker_movement_registered"] is False


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_remaining_blockers_tracked() -> None:
    packet = _json(PACKET_PATH)
    rows = packet["release_blocking_obligations_carry_forward"]
    assert packet["release_blocking_obligation_count"] == 4
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS
    assert all(row["remediation_execution_status"] == "not_executed_v0" for row in rows)

    other = packet["other_release_blocking_obligations"]
    assert packet["other_release_blocking_obligation_count"] == 3
    assert [row["dependency_finding_id"] for row in other] == OTHER_EXPECTED_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_003"
        assert row["modified_by_tranche_003"] is False


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_forbidden_effects_false() -> None:
    packet = _json(PACKET_PATH)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert packet["release_packet_assembled"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["validation_claim_authorized"] is False


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_next_target() -> None:
    packet = _json(PACKET_PATH)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == "status_adjudication_packet_result_review_only"
    assert packet["selection_count"] == 1
    assert packet["next_action_scope"] == (
        "REVIEW_TRANCHE_003_STATUS_ADJUDICATION_PACKET_RESULT_ONLY_NO_STATUS_DECISION_OR_BLOCKER_MOVEMENT"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_result": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_003_status_adjudication": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_STATUS_ADJUDICATION_PACKET_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_003_status_adjudication_packet_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche003StatusAdjudicationPacket" in index_text
    assert (
        "v01_dependency_remediation_tranche_003_status_adjudication_packet_does_not_move_blocker"
        in index_text
    )
