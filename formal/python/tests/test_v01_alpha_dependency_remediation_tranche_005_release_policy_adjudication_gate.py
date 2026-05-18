from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_report import (
    DEFAULT_CAPTURED_AT_UTC,
    EXECUTION_ID,
    EXPECTED_AXIOMS,
    LEAN_AUDIT_COMMAND,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    POLICY_CLASSIFICATION,
    POLICY_QUESTION,
    PROJECT_AXIOMS_USED,
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
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
    build_adjudication,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
ADJUDICATION_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_ADJUDICATION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche005ReleasePolicyAdjudication.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "remediation_closure_executed",
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
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


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert ADJUDICATION_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ADJUDICATION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_consumes_result_review() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["schema_id"] == SCHEMA_ID
    assert adjudication["execution_id"] == EXECUTION_ID
    assert adjudication["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert adjudication["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert adjudication["executed"] is True
    assert adjudication["accepted"] is True
    assert adjudication["outcome_id"] == OUTCOME_ID
    assert adjudication["consumes_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_v0"
    )
    assert adjudication["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_preserves_selected_dependency() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["execution_scope"] == (
        "EXECUTE_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_ONLY_NO_RELEASE_PROMOTION"
    )
    assert adjudication["tranche_001_status"] == TRANCHE_001_STATUS
    assert adjudication["tranche_002_status"] == TRANCHE_002_STATUS
    assert adjudication["tranche_003_status"] == TRANCHE_003_STATUS
    assert adjudication["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert adjudication["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert adjudication["selected_dependency"] == SELECTED_DEPENDENCY
    assert adjudication["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    selected = adjudication["selected_release_blocking_obligation"]
    assert selected["dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_preserves_evidence() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["lean_audit_target"]["lean_target"] == LEAN_TARGET
    assert adjudication["lean_audit_target"]["command"] == LEAN_AUDIT_COMMAND
    assert adjudication["lean_audit_target"]["exit_code"] == 0

    evidence = adjudication["accepted_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["exact_axioms_or_dependencies_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_or_mathlib_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
    assert evidence["project_local_axioms_present"] is False
    assert evidence["classification"] == "exact_dependency_evidence_produced_no_project_axioms_detected"
    assert "supplied_interface_alignment_semantics_construct_bridge_package_v0" in evidence[
        "raw_output"
    ]


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_decides_narrow_policy_question() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["policy_question"] == POLICY_QUESTION
    assert adjudication["policy_adjudication_executed"] is True
    assert adjudication["policy_decision_made"] is True
    assert adjudication["release_policy_decision_made"] is True
    assert adjudication["policy_classification"] == POLICY_CLASSIFICATION
    assert adjudication["policy_acceptance_for_standard_lean_axioms"] is True
    assert adjudication["documentation_requirement_open"] is True

    decision = adjudication["policy_decision"]
    assert decision["classification"] == POLICY_CLASSIFICATION
    assert decision["standard_lean_axioms_reviewed"] == EXPECTED_AXIOMS
    assert decision["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert decision["project_axiom_count"] == 0
    assert decision["expert_re_review_required"] is False
    assert decision["does_not_clear_blocker_by_itself"] is True
    assert decision["does_not_discharge_theorem_or_proof_debt"] is True
    assert decision["does_not_mark_release_readiness"] is True
    assert decision["does_not_move_retained_tranche_004"] is True
    assert decision["documentation_requirement"]
    assert any("not inferred by analogy alone" in basis for basis in decision["decision_basis"])


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_carries_tranche_004_and_006() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["tranche_004_status"] == TRANCHE_004_STATUS
    retained = adjudication["retained_tranche_004_carry_forward"]
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert adjudication["release_readiness_blocked_by_tranche_004"] is True
    assert adjudication["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert adjudication["tranche_004_retained_blocker_discharged"] is False

    assert adjudication["tranche_006_status"] == TRANCHE_006_STATUS
    tranche_006 = adjudication["tranche_006_obligation_carry_forward"]
    assert tranche_006["dependency_finding_id"] == TRANCHE_006_FINDING_ID
    assert tranche_006["dependency"] == TRANCHE_006_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_keeps_blockers_tracked() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["tranche_005_release_blocker_status"] == (
        "pending_result_review_policy_acceptable_with_documentation_requirement"
    )
    assert adjudication["remediation_closure_authorized"] is False
    assert adjudication["remediation_closure_executed"] is False
    assert adjudication["remediation_fully_satisfied"] is False
    assert adjudication["blocker_movement_authorized"] is False
    assert adjudication["blocker_movement_registered"] is False
    assert adjudication["post_adjudication_result_review_required"] is True

    rows = adjudication["release_blocking_obligations_carry_forward"]
    assert adjudication["release_blocking_obligation_count"] == 3
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

    other = adjudication["other_release_blocking_obligations"]
    assert adjudication["other_release_blocking_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in other] == [
        TRANCHE_004_FINDING_ID,
        TRANCHE_006_FINDING_ID,
    ]
    for row in other:
        assert row["modified_by_tranche_005_policy_adjudication"] is False


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_forbidden_effects_false() -> None:
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

    combined = json.dumps(adjudication, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_next_target() -> None:
    adjudication = _json(ADJUDICATION_PATH)
    assert adjudication["selected_next_target"] == NEXT_TARGET
    assert adjudication["selected_next_target_kind"] == (
        "release_policy_adjudication_result_review_only"
    )
    assert adjudication["selection_count"] == 1
    assert adjudication["next_action_scope"] == (
        "REVIEW_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_RESULT_ONLY_NO_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in adjudication["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_result": "selected",
        "prepare_v01_alpha_dependency_remediation_tranche_005_documentation_packet": "deferred",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        EXECUTION_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_005_RELEASE_POLICY_ADJUDICATION_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_005_release_policy_adjudication_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_ADJUDICATION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche005ReleasePolicyAdjudication" in index_text
    assert (
        "v01_dependency_remediation_tranche_005_release_policy_adjudication_does_not_promote_release"
        in index_text
    )
