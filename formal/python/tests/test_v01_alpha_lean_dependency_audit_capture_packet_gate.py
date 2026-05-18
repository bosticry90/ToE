from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_lean_dependency_audit_capture_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    build_capture_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
GAP_REVIEW_PATH = RELEASE_DIR / "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_20260515_v0.json"
CAPTURE_PACKET_PATH = (
    RELEASE_DIR / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_lean_dependency_audit_capture_packet_report.py"
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
    "Phase 2 authorized",
    "seam closure authorized",
    "empirical validation authorized",
    "master action promoted",
    "claim promoted",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_lean_dependency_audit_capture_packet_files_exist() -> None:
    assert GAP_REVIEW_PATH.exists()
    assert CAPTURE_PACKET_PATH.exists()
    assert TOOL_PATH.exists()


def test_v01_alpha_lean_dependency_audit_capture_packet_consumes_gap_review() -> None:
    payload = _json(CAPTURE_PACKET_PATH)
    assert payload["schema_id"] == "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0"
    assert payload["packet_id"] == "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0"
    assert payload["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert payload["classification"] == "P-POLICY/nonclaim"
    assert payload["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert payload["prepared"] is True
    assert payload["outcome_id"] == OUTCOME_ID
    assert payload["consumed_target"] == "prepare_v01_alpha_lean_dependency_audit_capture_packet"
    assert payload["consumes_gap_review"] == "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_v0"
    assert payload["consumes_gap_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_20260515_v0.json"
    )
    assert payload["source_gap_review_primary_gap"] == (
        "LEAN_DEPENDENCY_AUDIT_CAPTURE_AND_EXPERT_REVIEW_PACKET_NOT_READY"
    )
    assert (
        payload["packet_scope"]
        == "CAPTURE_DEPENDENCY_AUDIT_READINESS_ONLY_NO_DISCHARGE_OR_RELEASE_ASSEMBLY"
    )


def test_v01_alpha_lean_dependency_audit_capture_packet_captures_required_surfaces() -> None:
    payload = _json(CAPTURE_PACKET_PATH)
    for pointer_key in [
        "lean_aggregate_pointer",
        "lean_release_index_pointer",
        "lean_dependency_audit_pointer",
        "axiom_spec_backed_ledger_pointer",
        "axiom_refresh_result_review_pointer",
    ]:
        assert (REPO_ROOT / payload[pointer_key]).exists(), pointer_key

    assert payload["current_lean_build_status"] == {
        "release_index_command": (
            "Push-Location formal/toe_formal; lake env lean ToeFormal/Release/V01Index.lean; Pop-Location"
        ),
        "release_index_status": "passed_current_packet_validation",
        "full_aggregate_status": "not_run_by_this_packet",
        "interpretation": "release index checks current referenced theorem surfaces, but this is not theorem discharge",
    }


def test_v01_alpha_lean_dependency_audit_capture_packet_axiom_posture() -> None:
    payload = _json(CAPTURE_PACKET_PATH)
    posture = payload["axiom_ledger_posture"]
    assert posture["real_axiom_count"] == 59
    assert posture["real_sorry_or_admit_count"] == 0
    assert posture["real_axiom_file_count"] == 14
    assert posture["retained_assumption_count"] == 22
    assert posture["spec_backed_count"] == 37
    assert posture["blocks_full_pillar_target_count"] == 22
    assert posture["defaultNonAlias"] == "absent_from_unresolved_axiom_debt_and_lean_backed"
    assert posture["sampleRep32"] == "absent_from_unresolved_axiom_debt_and_lean_backed_constructor"
    assert posture["documentation_discharge_claim"] is False
    assert len(payload["known_retained_assumptions"]) == 22
    assert {row["class_id"]: row["row_count"] for row in payload["known_proof_debt_classes"]} == {
        "retained_assumption": 22,
        "spec_backed": 37,
        "blocks_full_pillar_target": 22,
    }


def test_v01_alpha_lean_dependency_audit_capture_packet_release_dependencies_remain_unresolved() -> None:
    payload = _json(CAPTURE_PACKET_PATH)
    summary = payload["capture_summary"]
    assert summary == {
        "v01_dependency_audit_row_count": 6,
        "release_index_check_count": 8,
        "relevant_module_count": 5,
        "release_blocking_dependency_count": 6,
        "expert_review_required_dependency_count": 6,
        "unresolved_dependency_count": 6,
        "primary_capture_gap": "EXACT_AXIOM_PRINT_OUTPUT_AND_EXPERT_REVIEW_NOT_EXECUTED_V0",
    }
    assert len(payload["v01_release_dependency_rows"]) == 6
    assert len(payload["release_index_checks"]) == 8
    assert len(payload["release_blocking_dependencies"]) == 6
    assert len(payload["expert_review_required_dependencies"]) == 6
    assert len(payload["unresolved_dependencies"]) == 6
    for row in payload["v01_release_dependency_rows"]:
        assert row["audit_status"] == "pending"
        assert row["release_dependency_class"] == "release_blocking_pending_capture"
        assert row["expert_review_required"] is True
        assert row["proof_debt_discharge_claim"] is False


def test_v01_alpha_lean_dependency_audit_capture_packet_preserves_boundaries() -> None:
    payload = _json(CAPTURE_PACKET_PATH)
    assert payload["expert_review_executed"] is False
    assert payload["release_packet_assembled"] is False
    assert payload["v01_alpha_marked_ready"] is False
    assert payload["lean_theorem_debt_discharged"] is False
    assert payload["axiom_spec_backed_debt_reduced_by_documentation"] is False
    forbidden = payload["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(payload, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_lean_dependency_audit_capture_packet_selects_result_review_only() -> None:
    payload = _json(CAPTURE_PACKET_PATH)
    assert payload["selected_next_target"] == NEXT_TARGET
    assert payload["selected_next_target_kind"] == "result_review_only"
    assert payload["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in payload["candidate_next_targets"]} == {
        "review_v01_alpha_lean_dependency_audit_capture_packet_result": "selected",
        "prepare_v01_alpha_expert_review_packet": "deferred",
        "prepare_v01_alpha_release_readiness_dependency_gap_adjudication": "deferred",
    }


def test_v01_alpha_lean_dependency_audit_capture_packet_acceptance_criteria_and_determinism() -> None:
    payload = _json(CAPTURE_PACKET_PATH)
    for key, value in payload["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_capture_packet(
        gap_review_path=GAP_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_capture_packet(
        gap_review_path=GAP_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert payload == generated_1


def test_v01_alpha_lean_dependency_audit_capture_packet_is_pinned_in_physics_roadmap() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0",
        "formal/docs/release/V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0.json",
        "formal/python/tools/v01_alpha_lean_dependency_audit_capture_packet_report.py",
        "formal/python/tests/test_v01_alpha_lean_dependency_audit_capture_packet_gate.py",
        "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_PREPARED_WITH_NO_RELEASE_ASSEMBLY_OR_PROOF_PROMOTION",
        "review_v01_alpha_lean_dependency_audit_capture_packet_result",
    ]
    for ref in refs:
        assert ref in roadmap_text
