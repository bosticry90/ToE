from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_expert_review_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
EXPERT_PACKET_PATH = RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_PACKET_20260515_v0.json"
REVIEW_PATH = RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_20260515_v0.json"
TOOL_PATH = (
    REPO_ROOT / "formal" / "python" / "tools" / "v01_alpha_expert_review_packet_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

FORBIDDEN_TRUE_KEYS = [
    "expert_review_executed",
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


def test_v01_alpha_expert_review_packet_result_review_files_exist() -> None:
    assert EXPERT_PACKET_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_v01_alpha_expert_review_packet_result_review_consumes_packet() -> None:
    review = _json(REVIEW_PATH)
    assert review["schema_id"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_expert_review_packet"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"
    assert review["consumes_expert_review_packet_pointer"] == (
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_PACKET_20260515_v0.json"
    )
    assert review["source_capture_review"] == "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_v0"
    assert review["source_capture_packet"] == "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0"


def test_v01_alpha_expert_review_packet_result_review_accepts_scope_only() -> None:
    review = _json(REVIEW_PATH)
    assert review["review_scope"] == "EXPERT_REVIEW_PACKET_RESULT_REVIEW_ONLY_NO_REVIEW_EXECUTION"
    assert review["review_scope_only_acceptance"] is True
    summary = review["packet_summary_reviewed"]
    assert summary["primary_packet_gap"] == "EXPERT_REVIEW_PACKET_PREPARED_BUT_REVIEW_NOT_EXECUTED_V0"
    assert summary["dependency_review_row_count"] == 6
    assert summary["release_blocking_dependency_count"] == 6
    assert summary["documentation_only_dependency_count"] == 3
    assert summary["expert_review_required_dependency_count"] == 6
    assert summary["retained_assumption_count"] == 22
    assert summary["proof_debt_class_count"] == 3


def test_v01_alpha_expert_review_packet_result_review_preserves_unexecuted_dependency_rows() -> None:
    review = _json(REVIEW_PATH)
    dependency = review["dependency_review_posture"]
    assert dependency["row_count"] == 6
    assert dependency["all_rows_not_executed"] is True
    assert dependency["reviewer_assessment_status"] == "prepared_not_assessed"
    assert dependency["proof_debt_discharge_claim_count"] == 0


def test_v01_alpha_expert_review_packet_result_review_retained_assumptions_remain_retained() -> None:
    review = _json(REVIEW_PATH)
    retained = review["retained_assumption_posture"]
    assert retained["row_count"] == 22
    assert retained["remain_retained"] is True
    assert retained["discharged_count_by_this_review"] == 0


def test_v01_alpha_expert_review_packet_result_review_forbidden_effects_false() -> None:
    review = _json(REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert review["expert_review_executed"] is False
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
        + _read(EXPERT_PACKET_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_expert_review_packet_result_review_selects_execution_packet_preparation_only() -> None:
    review = _json(REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "expert_review_execution_packet_preparation_only"
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == "PREPARE_EXECUTION_PACKET_ONLY_NO_EXPERT_REVIEW_EXECUTION"
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_expert_review_execution_packet": "selected",
        "execute_v01_alpha_expert_review": "deferred",
        "assemble_v01_alpha_public_release_packet": "deferred",
    }


def test_v01_alpha_expert_review_packet_result_review_acceptance_and_determinism() -> None:
    review = _json(REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        expert_packet_path=EXPERT_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        expert_packet_path=EXPERT_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_expert_review_packet_result_review_is_pinned() -> None:
    physics_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_v0",
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_expert_review_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_expert_review_packet_result_review_gate.py",
        "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_ACCEPTS_REVIEW_SCOPE_ONLY_AND_AUTHORIZES_EXPERT_REVIEW_EXECUTION_PACKET_PREPARATION_ONLY",
        "prepare_v01_alpha_expert_review_execution_packet",
    ]
    for ref in refs:
        assert ref in physics_text
