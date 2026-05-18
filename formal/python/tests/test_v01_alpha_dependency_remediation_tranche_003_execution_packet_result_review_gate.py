from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AUDIT_COMMAND,
    LEAN_SOURCE,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    REVIEW_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
PACKET_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_EXECUTION_PACKET_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche003ExecutionPacketResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "remediation_executed",
    "lean_dependency_audit_executed",
    "lean_dependency_evidence_captured",
    "documentation_prepared",
    "expert_re_review_executed",
    "blocker_movement_registered",
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


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_consumes_packet() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0"
    )
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_tranche_003_execution_packet"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_EXECUTION_PACKET_v0"
    )
    assert review["consumes_tranche_003_execution_packet_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_EXECUTION_PACKET_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_preserves_prior_tranches() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == "audit_target_accepted_pending_audit_execution"
    assert review["tranche_003_cleared_for_global_release_readiness"] is False
    assert review["global_release_readiness_still_blocked"] is True


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_selects_tranche_003_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selection_count"] == 1
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert review["selected_dependency"] == SELECTED_DEPENDENCY
    assert review["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    selected = review["selected_release_blocking_obligation"]
    assert selected["dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY
    assert selected["dependency_class"] == SELECTED_DEPENDENCY_CLASS


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_accepts_exact_audit_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    target = review["lean_dependency_audit_target"]
    required = review["required_evidence_surface"]
    assert review["tranche_003_execution_packet_accepted"] is True
    assert review["tranche_003_audit_target_accepted"] is True
    assert target["lean_target"] == LEAN_TARGET
    assert target["lean_source"] == LEAN_SOURCE
    assert target["audit_command"] == LEAN_AUDIT_COMMAND
    assert target["executed_by_this_packet"] is False
    assert target["executed_by_this_review"] is False
    assert required["lean_target"] == LEAN_TARGET
    assert required["audit_command"] == LEAN_AUDIT_COMMAND
    assert required["execution_status"] == "prepared_not_executed_v0"


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_carries_forward_four_blockers() -> None:
    review = _json(RESULT_REVIEW_PATH)
    rows = review["release_blocking_obligations_carry_forward"]
    assert review["release_blocking_obligation_count"] == 4
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS
    for row in rows:
        assert row["modified_by_tranche_002"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_002"


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_authorizes_audit_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["execution_packet_result_review_classification"] == (
        "audit_target_accepted_audit_execution_authorized_only"
    )
    assert review["tranche_003_audit_execution_authorized"] is True
    assert review["lean_dependency_audit_execution_authorized"] is True
    assert review["remediation_closure_execution_authorized"] is False
    assert review["lean_dependency_audit_executed"] is False
    assert review["lean_dependency_evidence_captured"] is False
    assert review["remediation_executed"] is False
    assert review["documentation_prepared"] is False


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_forbidden_effects_false() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "tranche_003_audit_execution_only"
    assert review["next_action_scope"] == (
        "EXECUTE_TRANCHE_003_LEAN_AUDIT_ONLY_NO_REMEDIATION_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "execute_v01_alpha_dependency_remediation_tranche_003_audit": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_003": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_003_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_003_execution_packet_result_review_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche003ExecutionPacketResultReview" in index_text
    assert (
        "v01_dependency_remediation_tranche_003_execution_packet_result_review_does_not_execute_audit"
        in index_text
    )
