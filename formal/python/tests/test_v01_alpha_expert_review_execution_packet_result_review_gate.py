from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_expert_review_execution_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
EXECUTION_PACKET_PATH = (
    RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_expert_review_execution_packet_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01ExpertReviewExecutionPacketResultReview.lean"
)
LEAN_INDEX_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
)

FORBIDDEN_TRUE_KEYS = [
    "expert_review_executed",
    "expert_review_conclusions_produced",
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
    "expert review executed true",
    "expert-review conclusions produced true",
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


def test_v01_alpha_expert_review_execution_packet_result_review_files_exist() -> None:
    assert EXECUTION_PACKET_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_expert_review_execution_packet_result_review_consumes_packet() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == (
        "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0"
    )
    assert review["review_id"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_execution_packet"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_v0"
    assert review["consumes_execution_packet_pointer"] == (
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_20260515_v0.json"
    )
    assert review["source_expert_review_packet"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"
    assert review["source_lean_dependency_audit_capture_packet"] == (
        "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0"
    )


def test_v01_alpha_expert_review_execution_packet_result_review_accepts_preparation_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_ONLY_NO_EXPERT_REVIEW_EXECUTION"
    )
    assert review["review_acceptance_posture"] == "execution_packet_accepted_as_preparation_only"
    assert review["expert_review_executed"] is False
    assert review["expert_review_conclusions_produced"] is False
    assert review["expert_review_execution_authorized"] is True
    assert review["expert_review_execution_authorization_scope"] == (
        "EXECUTE_EXPERT_REVIEW_PACKET_ONLY_NO_RELEASE_PROMOTION"
    )


def test_v01_alpha_expert_review_execution_packet_result_review_preserves_packet_summary() -> None:
    review = _json(RESULT_REVIEW_PATH)
    summary = review["packet_summary_reviewed"]
    assert summary["primary_packet_gap"] == "EXPERT_REVIEW_PACKET_PREPARED_BUT_REVIEW_NOT_EXECUTED_V0"
    assert summary["dependency_review_row_count"] == 6
    assert summary["release_blocking_dependency_count"] == 6
    assert summary["documentation_only_dependency_count"] == 3
    assert summary["expert_review_required_dependency_count"] == 6
    assert summary["retained_assumption_count"] == 22
    assert summary["proof_debt_class_count"] == 3
    assert summary["execution_schema_defined"] is True
    assert summary["review_conclusions_produced"] is False


def test_v01_alpha_expert_review_execution_packet_result_review_checks_contract() -> None:
    review = _json(RESULT_REVIEW_PATH)
    contract = review["execution_packet_review"]
    assert contract["sections_present"] is True
    assert contract["review_contract_complete"] is True
    assert contract["evidence_bundle_complete"] is True
    assert contract["output_schema_prepared"] is True
    assert contract["output_schema_produced_by_this_review"] is False
    assert contract["review_conclusions_produced_by_this_review"] is False


def test_v01_alpha_expert_review_execution_packet_result_review_retained_and_blocker_posture() -> None:
    review = _json(RESULT_REVIEW_PATH)
    retained = review["retained_assumption_posture"]
    assert retained["row_count"] == 22
    assert retained["remain_retained"] is True
    assert retained["discharged_count_by_this_review"] == 0

    dependency = review["dependency_review_posture"]
    assert dependency["row_count"] == 6
    assert dependency["release_blocking_dependency_count"] == 6
    assert dependency["release_blockers_remain_unmoved"] is True
    assert dependency["proof_debt_discharge_claim_count"] == 0


def test_v01_alpha_expert_review_execution_packet_result_review_forbidden_effects_false() -> None:
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

    boundary = review["authorization_boundary"]
    assert boundary["release_readiness_authorized"] is False
    assert boundary["release_packet_assembly_authorized"] is False
    assert boundary["theorem_or_proof_debt_discharge_authorized"] is False
    assert boundary["seam_or_master_action_promotion_authorized"] is False

    combined = (
        json.dumps(review, sort_keys=True)
        + "\n"
        + _read(EXECUTION_PACKET_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_expert_review_execution_packet_result_review_selects_execution_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "expert_review_execution_only"
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == "EXECUTE_EXPERT_REVIEW_PACKET_ONLY_NO_RELEASE_PROMOTION"
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "execute_v01_alpha_expert_review_packet": "selected",
        "remediate_v01_alpha_expert_review_execution_packet": "deferred",
        "assemble_v01_alpha_public_release_packet": "deferred",
    }


def test_v01_alpha_expert_review_execution_packet_result_review_acceptance_and_determinism() -> None:
    review = _json(RESULT_REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        execution_packet_path=EXECUTION_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        execution_packet_path=EXECUTION_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_expert_review_execution_packet_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_v0",
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_expert_review_execution_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_expert_review_execution_packet_result_review_gate.py",
        OUTCOME_ID,
        "execute_v01_alpha_expert_review_packet",
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01ExpertReviewExecutionPacketResultReview" in index_text
    assert "v01_expert_review_execution_packet_result_review_does_not_execute_review" in index_text
