from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_report import (
    CURRENT_BLOCKER_STATUS,
    DEFAULT_CAPTURED_AT_UTC,
    DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION,
    EXECUTION_ID,
    EXPECTED_AXIOMS,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    POLICY_CLASSIFICATION,
    PROJECT_AXIOMS_USED,
    REGISTERED_BLOCKER_STATUS,
    REGISTERED_MOVEMENT,
    REGISTERED_MOVEMENT_TOKEN,
    REGISTRATION_CLASSIFICATION,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_REMEDIATION_FINDING_ID,
    SELECTED_TRANCHE_ID,
    STATUS_CANDIDATE,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    build_registration,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
REGISTRATION_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_REGISTRATION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche003BlockerMovementRegistration.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "blocker_fully_remediated",
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


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert REGISTRATION_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REGISTRATION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_consumes_result_review() -> None:
    registration = _json(REGISTRATION_PATH)
    assert registration["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_20260515_v0"
    )
    assert registration["execution_id"] == EXECUTION_ID
    assert registration["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert registration["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert registration["executed"] is True
    assert registration["accepted"] is True
    assert registration["outcome_id"] == OUTCOME_ID
    assert registration["consumes_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW_v0"
    )
    assert registration["consumes_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_selected_dependency() -> None:
    registration = _json(REGISTRATION_PATH)
    assert registration["execution_scope"] == (
        "EXECUTE_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_ONLY_NO_RELEASE_PROMOTION_OR_GLOBAL_DEBT_DISCHARGE"
    )
    assert registration["tranche_001_status"] == TRANCHE_001_STATUS
    assert registration["tranche_002_status"] == TRANCHE_002_STATUS
    assert registration["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert registration["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert registration["selected_dependency"] == SELECTED_DEPENDENCY
    assert registration["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert registration["lean_audit_target"]["lean_target"] == LEAN_TARGET


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_exact_movement() -> None:
    registration = _json(REGISTRATION_PATH)
    movement = registration["registered_movement"]
    assert movement["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert movement["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert movement["selected_dependency"] == SELECTED_DEPENDENCY
    assert movement["previous_status"] == CURRENT_BLOCKER_STATUS
    assert movement["registered_status"] == REGISTERED_BLOCKER_STATUS
    assert movement["registered_movement"] == REGISTERED_MOVEMENT
    assert movement["registered_movement_token"] == REGISTERED_MOVEMENT_TOKEN
    assert movement["movement_scope"] == "tranche_003_only"
    assert movement["registered_by_this_execution"] is True
    assert movement["tranche_001_status"] == TRANCHE_001_STATUS
    assert movement["tranche_002_status"] == TRANCHE_002_STATUS
    assert registration["previous_blocker_status"] == CURRENT_BLOCKER_STATUS
    assert registration["registered_blocker_status"] == REGISTERED_BLOCKER_STATUS
    assert registration["registered_movement_name"] == REGISTERED_MOVEMENT
    assert registration["registered_movement_token"] == REGISTERED_MOVEMENT_TOKEN


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_preserves_evidence_policy_documentation_chain() -> None:
    registration = _json(REGISTRATION_PATH)
    evidence = registration["accepted_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["exact_axioms_or_dependencies_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_or_mathlib_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
    assert evidence["project_local_axioms_present"] is False
    assert evidence["classification"] == "exact_dependency_evidence_produced_no_project_axioms_detected"
    assert registration["policy_classification"] == POLICY_CLASSIFICATION
    assert (
        registration["documentation_result_review_classification"]
        == DOCUMENTATION_RESULT_REVIEW_CLASSIFICATION
    )
    assert registration["documentation_accepted_only_as_documentation"] is True
    assert registration["documentation_surface"]["exists"] is True
    assert registration["documentation_surface"]["accepted_as_documentation"] is True
    assert registration["status_candidate_reviewed"] == STATUS_CANDIDATE


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_registers_only_pending_review() -> None:
    registration = _json(REGISTRATION_PATH)
    movement = registration["registered_movement"]
    assert registration["blocker_movement_registration_executed"] is True
    assert registration["blocker_movement_registered"] is True
    assert registration["blocker_movement_registration_result_classification"] == (
        REGISTRATION_CLASSIFICATION
    )
    assert registration["post_registration_result_review_required"] is True
    assert registration["tranche_003_formal_movement_accepted"] is False
    assert registration["tranche_003_cleared_for_global_release_readiness"] is False
    assert registration["tranche_003_release_blocker_status"] == (
        "documented_dependency_nonblocking_pending_registration_result_review"
    )
    assert registration["remediation_fully_satisfied"] is False
    assert registration["blocker_fully_remediated"] is False
    assert movement["requires_result_review_for_formal_acceptance"] is True


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_remaining_blockers_tracked() -> None:
    registration = _json(REGISTRATION_PATH)
    rows = registration["release_blocking_obligations_carry_forward"]
    assert registration["release_blocking_obligation_count"] == 4
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS

    other = registration["other_release_blocking_obligations"]
    assert registration["other_release_blocking_obligation_count"] == 3
    assert (
        registration["remaining_release_blocking_obligation_count_excluding_tranche_003_candidate"]
        == 3
    )
    assert [row["dependency_finding_id"] for row in other] == OTHER_EXPECTED_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_003"
        assert row["modified_by_tranche_003"] is False


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_forbidden_effects_false() -> None:
    registration = _json(REGISTRATION_PATH)
    forbidden = registration["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert registration["release_packet_assembled"] is False
    assert registration["v01_alpha_marked_ready"] is False
    assert registration["lean_theorem_debt_discharged"] is False
    assert registration["axiom_spec_backed_debt_reduced"] is False
    assert registration["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert registration["proof_debt_reduced"] is False
    assert registration["retained_assumptions_discharged"] is False
    assert registration["validation_claim_authorized"] is False


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_next_target() -> None:
    registration = _json(REGISTRATION_PATH)
    assert registration["selected_next_target"] == NEXT_TARGET
    assert registration["selected_next_target_kind"] == (
        "blocker_movement_registration_result_review_only"
    )
    assert registration["selection_count"] == 1
    assert registration["next_action_scope"] == (
        "REVIEW_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_RESULT_ONLY_NO_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in registration["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_result": "selected",
        "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_acceptance_and_determinism() -> None:
    registration = _json(REGISTRATION_PATH)
    for key, value in registration["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_registration(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_registration(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert registration == generated_1


def test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        EXECUTION_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_BLOCKER_MOVEMENT_REGISTRATION_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_003_blocker_movement_registration_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_REGISTRATION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche003BlockerMovementRegistration" in index_text
    assert (
        "v01_dependency_remediation_tranche_003_blocker_movement_registration_does_not_promote_release"
        in index_text
    )
