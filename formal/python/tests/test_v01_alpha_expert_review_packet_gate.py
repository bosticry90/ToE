from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_expert_review_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    build_expert_review_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
CAPTURE_REVIEW_PATH = (
    RELEASE_DIR / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_20260515_v0.json"
)
CAPTURE_PACKET_PATH = (
    RELEASE_DIR / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0.json"
)
EXPERT_PACKET_PATH = RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_PACKET_20260515_v0.json"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "v01_alpha_expert_review_packet_report.py"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

FORBIDDEN_TRUE_KEYS = [
    "expert_review_executed",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
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
    "proof debt reduced true",
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


def test_v01_alpha_expert_review_packet_files_exist() -> None:
    assert CAPTURE_REVIEW_PATH.exists()
    assert CAPTURE_PACKET_PATH.exists()
    assert EXPERT_PACKET_PATH.exists()
    assert TOOL_PATH.exists()


def test_v01_alpha_expert_review_packet_consumes_capture_result_review() -> None:
    packet = _json(EXPERT_PACKET_PATH)
    assert packet["schema_id"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_20260515_v0"
    assert packet["packet_id"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["classification"] == "P-POLICY/nonclaim"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumed_target"] == "prepare_v01_alpha_expert_review_packet"
    assert packet["consumes_result_review"] == (
        "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_v0"
    )
    assert packet["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_20260515_v0.json"
    )
    assert packet["source_capture_packet"] == "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0"
    assert packet["source_gap_review_primary_gap"] == (
        "LEAN_DEPENDENCY_AUDIT_CAPTURE_AND_EXPERT_REVIEW_PACKET_NOT_READY"
    )


def test_v01_alpha_expert_review_packet_prepares_review_scope_only() -> None:
    packet = _json(EXPERT_PACKET_PATH)
    assert packet["packet_scope"] == "PREPARE_EXPERT_REVIEW_PACKET_ONLY_NO_REVIEW_EXECUTION_OR_RELEASE_ASSEMBLY"
    assert packet["review_execution_status"] == "not_executed_v0"
    assert packet["source_capture_gap"] == "EXACT_AXIOM_PRINT_OUTPUT_AND_EXPERT_REVIEW_NOT_EXECUTED_V0"
    scope = packet["review_scope"]
    expected_scope_keys = {
        "lean_dependency_audit_posture",
        "axiom_spec_backed_ledger_posture",
        "retained_assumptions",
        "release_blocking_dependencies",
        "documentation_only_dependencies",
        "expert_review_required_dependencies",
        "proof_debt_categories",
        "unresolved_theorem_seam_master_action_blockers",
    }
    assert set(scope) == expected_scope_keys
    for row in scope.values():
        assert row["reviewer_task"]


def test_v01_alpha_expert_review_packet_captures_required_counts_and_rows() -> None:
    packet = _json(EXPERT_PACKET_PATH)
    summary = packet["packet_summary"]
    assert summary["dependency_review_row_count"] == 6
    assert summary["release_blocking_dependency_count"] == 6
    assert summary["documentation_only_dependency_count"] == 3
    assert summary["expert_review_required_dependency_count"] == 6
    assert summary["retained_assumption_count"] == 22
    assert summary["proof_debt_class_count"] == 3
    assert summary["primary_packet_gap"] == "EXPERT_REVIEW_PACKET_PREPARED_BUT_REVIEW_NOT_EXECUTED_V0"

    assert len(packet["dependency_review_rows"]) == 6
    for row in packet["dependency_review_rows"]:
        assert row["expert_review_required"] is True
        assert row["review_execution_status"] == "not_executed_v0"
        assert row["reviewer_assessment_status"] == "prepared_not_assessed"
        assert row["proof_debt_discharge_claim"] is False


def test_v01_alpha_expert_review_packet_forbidden_effects_false() -> None:
    packet = _json(EXPERT_PACKET_PATH)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert packet["expert_review_executed"] is False
    assert packet["release_packet_assembled"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert packet["proof_debt_reduced"] is False

    combined = (
        json.dumps(packet, sort_keys=True)
        + "\n"
        + _read(CAPTURE_REVIEW_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_expert_review_packet_reviewer_is_not_allowed_to_promote() -> None:
    packet = _json(EXPERT_PACKET_PATH)
    assert packet["reviewer_not_allowed_to_promote"] == [
        "expert review execution",
        "v0.1-alpha release packet assembly",
        "v0.1-alpha readiness",
        "Lean theorem debt discharge",
        "axiom/spec-backed proof debt reduction",
        "Phase 2 authorization",
        "seam closure",
        "empirical validation",
        "master-action promotion",
        "claim promotion",
    ]
    assert len(packet["reviewer_assessment_questions"]) == 5


def test_v01_alpha_expert_review_packet_selects_result_review_only() -> None:
    packet = _json(EXPERT_PACKET_PATH)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == "result_review_only"
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        "review_v01_alpha_expert_review_packet_result": "selected",
        "prepare_v01_alpha_expert_review_execution_packet": "deferred",
        "prepare_v01_alpha_release_readiness_dependency_gap_adjudication": "deferred",
    }


def test_v01_alpha_expert_review_packet_acceptance_and_determinism() -> None:
    packet = _json(EXPERT_PACKET_PATH)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_expert_review_packet(
        capture_review_path=CAPTURE_REVIEW_PATH,
        capture_packet_path=CAPTURE_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_expert_review_packet(
        capture_review_path=CAPTURE_REVIEW_PATH,
        capture_packet_path=CAPTURE_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_expert_review_packet_is_pinned() -> None:
    physics_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_EXPERT_REVIEW_PACKET_v0",
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_PACKET_20260515_v0.json",
        "formal/python/tools/v01_alpha_expert_review_packet_report.py",
        "formal/python/tests/test_v01_alpha_expert_review_packet_gate.py",
        "V01_ALPHA_EXPERT_REVIEW_PACKET_PREPARED_FROM_LEAN_DEPENDENCY_AUDIT_CAPTURE_WITH_NO_REVIEW_EXECUTION_OR_RELEASE_PROMOTION",
        "review_v01_alpha_expert_review_packet_result",
    ]
    for ref in refs:
        assert ref in physics_text
