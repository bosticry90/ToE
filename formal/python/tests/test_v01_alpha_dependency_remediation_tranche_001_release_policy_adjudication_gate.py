from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_report import (
    DEFAULT_CAPTURED_AT_UTC,
    EXPECTED_AXIOMS,
    NEXT_TARGET,
    OUTCOME_ID,
    POLICY_CLASSIFICATION,
    POLICY_QUESTION,
    SELECTED_DEPENDENCY,
    SELECTED_REMEDIATION_FINDING_ID,
    SELECTED_TRANCHE_ID,
    build_adjudication,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
ADJUDICATION_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_ADJUDICATION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche001ReleasePolicyAdjudication.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
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


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert ADJUDICATION_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ADJUDICATION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_consumes_result_review() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_20260515_v0"
    )
    assert adjudication["execution_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_v0"
    )
    assert adjudication["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert adjudication["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert adjudication["executed"] is True
    assert adjudication["accepted"] is True
    assert adjudication["outcome_id"] == OUTCOME_ID
    assert adjudication["consumes_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_v0"
    )
    assert adjudication["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_preserves_selected_dependency() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["execution_scope"] == (
        "EXECUTE_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_ONLY_NO_RELEASE_PROMOTION"
    )
    assert adjudication["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert adjudication["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert adjudication["selected_dependency"] == SELECTED_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_preserves_evidence() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    evidence = adjudication["accepted_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["project_axioms_used"] == []
    assert evidence["project_axiom_count"] == 0
    assert evidence["classification"] == "exact_dependency_evidence_produced_no_project_axioms_detected"
    assert "propext" in evidence["raw_output"]
    assert "Classical.choice" in evidence["raw_output"]
    assert "Quot.sound" in evidence["raw_output"]


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_decides_narrow_policy_question() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["policy_question"] == POLICY_QUESTION
    assert adjudication["policy_adjudication_executed"] is True
    assert adjudication["policy_decision_made"] is True
    assert adjudication["policy_classification"] == POLICY_CLASSIFICATION
    assert adjudication["policy_acceptance_for_standard_lean_axioms"] is True
    assert adjudication["documentation_requirement_open"] is True

    decision = adjudication["policy_decision"]
    assert decision["classification"] == POLICY_CLASSIFICATION
    assert decision["standard_lean_axioms_reviewed"] == EXPECTED_AXIOMS
    assert decision["project_axioms_used"] == []
    assert decision["project_axiom_count"] == 0
    assert decision["does_not_clear_blocker_by_itself"] is True
    assert decision["does_not_discharge_theorem_or_proof_debt"] is True
    assert decision["does_not_mark_release_readiness"] is True
    assert decision["documentation_requirement"]


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_keeps_blockers_tracked() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["tranche_001_release_blocker_status"] == (
        "pending_result_review_policy_acceptable_with_documentation_requirement"
    )
    assert adjudication["remediation_fully_satisfied"] is False
    assert adjudication["blocker_movement_authorized"] is False
    assert adjudication["post_adjudication_result_review_required"] is True

    other = adjudication["other_release_blocking_obligations"]
    assert adjudication["other_release_blocking_obligation_count"] == 5
    assert [row["dependency_finding_id"] for row in other] == OTHER_EXPECTED_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_executed_in_tranche_001"
        assert row["modified_by_tranche_001"] is False


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_forbidden_effects_false() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_next_target() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["selected_next_target"] == NEXT_TARGET
    assert adjudication["selected_next_target_kind"] == (
        "release_policy_adjudication_result_review_only"
    )
    assert adjudication["selection_count"] == 1
    assert adjudication["next_action_scope"] == (
        "REVIEW_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_RESULT_ONLY_NO_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in adjudication["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_result": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_002": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_v0",
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_RELEASE_POLICY_ADJUDICATION_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_001_release_policy_adjudication_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_ADJUDICATION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche001ReleasePolicyAdjudication" in index_text
    assert (
        "v01_dependency_remediation_tranche_001_release_policy_adjudication_does_not_promote_release"
        in index_text
    )
