from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_expert_review_execution_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
EXECUTION_PATH = RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_20260515_v0.json"
RESULT_REVIEW_PATH = RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_20260515_v0.json"
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_expert_review_execution_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01ExpertReviewExecutionResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "blocker_movement_authorized",
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


def test_v01_alpha_expert_review_execution_result_review_files_exist() -> None:
    assert EXECUTION_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_expert_review_execution_result_review_consumes_execution() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_execution"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_v0"
    assert review["consumes_execution_pointer"] == (
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_EXECUTION_20260515_v0.json"
    )
    assert review["source_execution_packet"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_v0"
    assert review["source_expert_review_packet"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"


def test_v01_alpha_expert_review_execution_result_review_accepts_evidence_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == "EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_ONLY_NO_RELEASE_PROMOTION"
    assert review["review_acceptance_posture"] == (
        "expert_review_evidence_accepted_with_dependency_remediation_required"
    )
    assert review["execution_outcome_reviewed"] == (
        "V01_ALPHA_EXPERT_REVIEW_EXECUTED_AS_REVIEW_EVIDENCE_ONLY_WITH_NO_RELEASE_PROMOTION"
    )
    summary = review["review_evidence_summary"]
    assert summary["release_blocking_dependency_finding_count"] == 6
    assert summary["documentation_only_dependency_finding_count"] == 3
    assert summary["expert_review_required_dependency_finding_count"] == 6
    assert summary["retained_assumption_finding_count"] == 22
    assert summary["proof_debt_class_count"] == 3
    assert summary["lean_dependency_row_count"] == 6
    assert summary["unresolved_blocker_finding_count"] == 6
    assert summary["release_promotion_recommended"] is False
    assert summary["release_readiness_adjudication_pending"] is True


def test_v01_alpha_expert_review_execution_result_review_summarizes_actual_findings() -> None:
    review = _json(RESULT_REVIEW_PATH)
    findings = review["actual_findings_summary"]
    assert len(findings["release_blocking_dependencies"]) == 6
    for row in findings["release_blocking_dependencies"]:
        assert row["blocks_v01_alpha_release_packet"] is True
        assert row["requires_remediation_before_release_assembly"] is True
        assert row["proof_debt_discharge_claim"] is False

    retained = findings["retained_assumptions"]
    assert retained["row_count"] == 22
    assert retained["remain_retained"] is True
    assert retained["discharged_by_execution_count"] == 0

    assert findings["proof_debt"]["class_count"] == 3
    assert findings["proof_debt"]["proof_debt_reduced_by_execution"] is False
    assert findings["lean_dependency"]["dependency_row_count"] == 6
    assert findings["lean_dependency"]["theorem_debt_discharged_by_execution"] is False
    assert findings["axiom_spec_backed_ledger"]["debt_reduced_by_execution"] is False
    assert len(findings["unresolved_blockers"]) == 6


def test_v01_alpha_expert_review_execution_result_review_routes_to_remediation() -> None:
    review = _json(RESULT_REVIEW_PATH)
    routing = review["routing_decision"]
    assert routing["remediation_required_before_release_assembly"] is True
    assert routing["release_readiness_adjudication_preparation_authorized"] is False
    assert routing["dependency_remediation_packet_preparation_authorized"] is True
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "dependency_remediation_packet_preparation_only"
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == "PREPARE_DEPENDENCY_REMEDIATION_PACKET_ONLY_NO_RELEASE_PROMOTION"
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_dependency_remediation_packet": "selected",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
        "assemble_v01_alpha_public_release_packet": "deferred",
    }


def test_v01_alpha_expert_review_execution_result_review_forbidden_effects_false() -> None:
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

    combined = (
        json.dumps(review, sort_keys=True)
        + "\n"
        + _read(EXECUTION_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_expert_review_execution_result_review_acceptance_and_determinism() -> None:
    review = _json(RESULT_REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        execution_path=EXECUTION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        execution_path=EXECUTION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_expert_review_execution_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_v0",
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_expert_review_execution_result_review_report.py",
        "formal/python/tests/test_v01_alpha_expert_review_execution_result_review_gate.py",
        OUTCOME_ID,
        "prepare_v01_alpha_dependency_remediation_packet",
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01ExpertReviewExecutionResultReview" in index_text
    assert "v01_expert_review_execution_result_review_does_not_promote_release" in index_text
