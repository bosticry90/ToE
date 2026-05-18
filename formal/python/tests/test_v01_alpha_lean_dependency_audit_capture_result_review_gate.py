from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_lean_dependency_audit_capture_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
CAPTURE_PACKET_PATH = (
    RELEASE_DIR / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0.json"
)
REVIEW_PATH = (
    RELEASE_DIR / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_lean_dependency_audit_capture_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

FORBIDDEN_TRUE_KEYS = [
    "expert_review_executed",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
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
    "proof debt reduced by documentation true",
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


def test_v01_alpha_lean_dependency_audit_capture_result_review_files_exist() -> None:
    assert CAPTURE_PACKET_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_v01_alpha_lean_dependency_audit_capture_result_review_consumes_capture_packet() -> None:
    review = _json(REVIEW_PATH)
    assert review["schema_id"] == "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_capture_packet"] == "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0"
    assert review["consumes_capture_packet_pointer"] == (
        "formal/docs/release/V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0.json"
    )
    assert review["source_gap_review"] == "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_v0"
    assert (
        review["source_gap_review_primary_gap"]
        == "LEAN_DEPENDENCY_AUDIT_CAPTURE_AND_EXPERT_REVIEW_PACKET_NOT_READY"
    )


def test_v01_alpha_lean_dependency_audit_capture_result_review_accepts_capture_only() -> None:
    review = _json(REVIEW_PATH)
    assert review["review_scope"] == "CAPTURE_RESULT_REVIEW_ONLY_NO_EXPERT_REVIEW_EXECUTION_OR_RELEASE_ASSEMBLY"
    assert review["capture_only_acceptance"] is True
    boundary = review["capture_packet_boundary_confirmed"]
    assert boundary == {
        "captured_dependency_posture_is_not_reviewed_dependency_posture": True,
        "captured_audit_packet_is_not_release_readiness": True,
        "documentation_is_not_theorem_discharge": True,
        "documentation_is_not_proof_debt_reduction": True,
    }


def test_v01_alpha_lean_dependency_audit_capture_result_review_preserves_counts_and_gaps() -> None:
    review = _json(REVIEW_PATH)
    summary = review["capture_summary_reviewed"]
    assert summary["primary_capture_gap"] == "EXACT_AXIOM_PRINT_OUTPUT_AND_EXPERT_REVIEW_NOT_EXECUTED_V0"
    assert summary["v01_dependency_audit_row_count"] == 6
    assert summary["release_index_check_count"] == 8
    assert summary["relevant_module_count"] == 5
    assert summary["release_blocking_dependency_count"] == 6
    assert summary["expert_review_required_dependency_count"] == 6
    assert summary["unresolved_dependency_count"] == 6

    axiom = review["axiom_ledger_posture_reviewed"]
    assert axiom["real_axiom_count"] == 59
    assert axiom["real_sorry_or_admit_count"] == 0
    assert axiom["retained_assumption_count"] == 22
    assert axiom["spec_backed_count"] == 37
    assert axiom["blocks_full_pillar_target_count"] == 22


def test_v01_alpha_lean_dependency_audit_capture_result_review_forbidden_effects_false() -> None:
    review = _json(REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert review["expert_review_executed"] is False
    assert review["release_packet_assembled"] is False
    assert review["v01_alpha_marked_ready"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert review["validation_claim_authorized"] is False

    combined = (
        json.dumps(review, sort_keys=True)
        + "\n"
        + _read(CAPTURE_PACKET_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_lean_dependency_audit_capture_result_review_selects_expert_review_packet_preparation_only() -> None:
    review = _json(REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "expert_review_packet_preparation_only"
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == "PREPARE_EXPERT_REVIEW_PACKET_ONLY_NO_EXPERT_REVIEW_EXECUTION"
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_expert_review_packet": "selected",
        "execute_v01_alpha_expert_review": "deferred",
        "assemble_v01_alpha_public_release_packet": "deferred",
    }


def test_v01_alpha_lean_dependency_audit_capture_result_review_acceptance_and_determinism() -> None:
    review = _json(REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        capture_packet_path=CAPTURE_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        capture_packet_path=CAPTURE_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_lean_dependency_audit_capture_result_review_is_pinned() -> None:
    physics_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_v0",
        "formal/docs/release/V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_lean_dependency_audit_capture_result_review_report.py",
        "formal/python/tests/test_v01_alpha_lean_dependency_audit_capture_result_review_gate.py",
        "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_ACCEPTS_CAPTURE_ONLY_AND_AUTHORIZES_EXPERT_REVIEW_PACKET_PREPARATION_ONLY",
        "prepare_v01_alpha_expert_review_packet",
    ]
    for ref in refs:
        assert ref in physics_text
