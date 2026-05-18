from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_expert_review_execution_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    REQUIRED_EXECUTION_PACKET_SECTIONS,
    build_execution_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_20260515_v0.json"
)
EXECUTION_PACKET_PATH = (
    RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_expert_review_execution_packet_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_EXECUTION_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01ExpertReviewExecutionPacket.lean"
)
LEAN_INDEX_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
)

FORBIDDEN_TRUE_KEYS = [
    "expert_review_executed",
    "expert_review_execution_authorized",
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
    "expert review conclusions produced true",
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


def test_v01_alpha_expert_review_execution_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert EXECUTION_PACKET_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_EXECUTION_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_expert_review_execution_packet_consumes_result_review() -> None:
    packet = _json(EXECUTION_PACKET_PATH)
    assert packet["schema_id"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_20260515_v0"
    assert packet["packet_id"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_v0"
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["classification"] == "P-POLICY/nonclaim"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumed_target"] == "prepare_v01_alpha_expert_review_execution_packet"
    assert packet["consumes_result_review"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_v0"
    assert packet["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_PACKET_RESULT_REVIEW_20260515_v0.json"
    )
    assert packet["source_expert_review_packet"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"
    assert packet["source_lean_dependency_audit_capture_packet"] == (
        "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0"
    )


def test_v01_alpha_expert_review_execution_packet_prepares_wrapper_only() -> None:
    packet = _json(EXECUTION_PACKET_PATH)
    assert packet["packet_scope"] == (
        "PREPARE_EXPERT_REVIEW_EXECUTION_PACKET_ONLY_NO_REVIEW_EXECUTION_OR_RELEASE_PROMOTION"
    )
    assert packet["execution_status"] == "not_executed_v0"
    assert packet["expert_review_executed"] is False
    assert packet["expert_review_execution_authorized"] is False
    assert packet["expert_review_conclusions_produced"] is False
    assert packet["review_conclusions"] == {
        "produced": False,
        "items": [],
        "reason": "execution_packet_preparation_only",
    }
    execution_packet = packet["execution_packet"]
    assert set(execution_packet) == REQUIRED_EXECUTION_PACKET_SECTIONS
    assert execution_packet["review_scope_boundaries"]["this_packet_executes_expert_review"] is False
    assert (
        execution_packet["review_scope_boundaries"][
            "this_packet_authorizes_expert_review_execution"
        ]
        is False
    )
    assert (
        execution_packet["review_scope_boundaries"]["this_packet_produces_review_conclusions"]
        is False
    )


def test_v01_alpha_expert_review_execution_packet_defines_required_review_contract() -> None:
    packet = _json(EXECUTION_PACKET_PATH)
    execution_packet = packet["execution_packet"]
    assert len(execution_packet["reviewer_inputs"]) == 5
    assert len(execution_packet["reviewer_questions"]) == 5
    assert len(execution_packet["review_acceptance_criteria"]) == 5
    assert len(execution_packet["review_failure_criteria"]) == 4

    evidence = execution_packet["evidence_bundle_pointers"]
    for key in [
        "expert_review_packet_result_review",
        "expert_review_packet",
        "lean_dependency_audit_capture_packet",
        "lean_dependency_audit_table",
        "lean_release_index",
        "axiom_spec_backed_ledger",
    ]:
        assert evidence[key]

    output_schema = execution_packet["expert_review_output_schema"]
    assert output_schema["schema_id"] == "V01_ALPHA_EXPERT_REVIEW_OUTPUT_SCHEMA_v0"
    assert output_schema["schema_prepared"] is True
    assert output_schema["output_produced_by_this_packet"] is False
    assert output_schema["conclusions_produced_by_this_packet"] is False
    assert "dependency_row_assessments" in output_schema["required_fields"]
    assert "release_ready" in output_schema["forbidden_output_claims"]

    adjudication = execution_packet["post_review_adjudication_rules"]
    assert adjudication["result_review_required_before_execution"] is True
    assert adjudication["next_review_target"] == NEXT_TARGET
    assert adjudication["execution_after_this_packet"] == "not_authorized"


def test_v01_alpha_expert_review_execution_packet_preserves_dependency_and_assumption_posture() -> None:
    packet = _json(EXECUTION_PACKET_PATH)
    summary = packet["packet_summary"]
    assert summary["primary_packet_gap"] == "EXPERT_REVIEW_PACKET_PREPARED_BUT_REVIEW_NOT_EXECUTED_V0"
    assert summary["dependency_review_row_count"] == 6
    assert summary["release_blocking_dependency_count"] == 6
    assert summary["documentation_only_dependency_count"] == 3
    assert summary["expert_review_required_dependency_count"] == 6
    assert summary["retained_assumption_count"] == 22
    assert summary["proof_debt_class_count"] == 3
    assert summary["execution_schema_defined"] is True
    assert summary["review_conclusions_produced"] is False

    retained = packet["execution_packet"]["retained_assumption_review_expectations"]
    assert retained["row_count"] == 22
    assert retained["expected_status"] == "retained_assumption"
    assert retained["remain_retained_through_this_packet"] is True
    assert retained["discharge_allowed_by_this_packet"] is False

    blockers = packet["execution_packet"]["release_blocking_dependency_review_expectations"]
    assert blockers["row_count"] == 6
    assert len(blockers["dependency_names"]) == 6
    assert blockers["release_blocker_status_changes_allowed_by_this_packet"] is False


def test_v01_alpha_expert_review_execution_packet_forbidden_effects_false() -> None:
    packet = _json(EXECUTION_PACKET_PATH)
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

    combined = (
        json.dumps(packet, sort_keys=True)
        + "\n"
        + _read(RESULT_REVIEW_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_expert_review_execution_packet_selects_result_review_only() -> None:
    packet = _json(EXECUTION_PACKET_PATH)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == "result_review_only"
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        "review_v01_alpha_expert_review_execution_packet_result": "selected",
        "execute_v01_alpha_expert_review_packet": "deferred",
        "assemble_v01_alpha_public_release_packet": "deferred",
    }


def test_v01_alpha_expert_review_execution_packet_acceptance_and_determinism() -> None:
    packet = _json(EXECUTION_PACKET_PATH)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_execution_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_execution_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_expert_review_execution_packet_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_v0",
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_20260515_v0.json",
        "formal/python/tools/v01_alpha_expert_review_execution_packet_report.py",
        "formal/python/tests/test_v01_alpha_expert_review_execution_packet_gate.py",
        OUTCOME_ID,
        "review_v01_alpha_expert_review_execution_packet_result",
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_EXECUTION_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01ExpertReviewExecutionPacket" in index_text
    assert "v01_expert_review_execution_packet_preparation_only" in index_text
