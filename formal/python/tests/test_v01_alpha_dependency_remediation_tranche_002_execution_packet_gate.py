from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_002_execution_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AUDIT_COMMAND,
    LEAN_SOURCE,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    TRANCHE_001_STATUS,
    build_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
SELECTION_RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
PACKET_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_002_execution_packet_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche002ExecutionPacket.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "remediation_execution_authorized",
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
    "V01-ALPHA-DEP-REM-002",
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


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_files_exist() -> None:
    assert SELECTION_RESULT_REVIEW_PATH.exists()
    assert PACKET_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_consumes_selection_result_review() -> None:
    packet = _json(PACKET_PATH)
    assert packet["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_20260515_v0"
    )
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_selection_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_RESULT_REVIEW_v0"
    )
    assert packet["consumes_selection_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_NEXT_TRANCHE_SELECTION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_preserves_tranche_001() -> None:
    packet = _json(PACKET_PATH)
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_001_formal_movement_accepted"] is True
    assert packet["tranche_001_cleared_for_global_release_readiness"] is False
    assert packet["global_release_readiness_still_blocked"] is True


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_selects_only_tranche_002() -> None:
    packet = _json(PACKET_PATH)
    assert packet["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert packet["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert packet["selected_dependency"] == SELECTED_DEPENDENCY
    assert packet["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    selected = packet["selected_release_blocking_obligation"]
    assert selected["dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY
    assert selected["dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert packet["selection_count"] == 1


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_tracks_all_five_blockers() -> None:
    packet = _json(PACKET_PATH)
    rows = packet["release_blocking_obligations_carry_forward"]
    assert packet["release_blocking_obligation_count"] == 5
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS
    assert packet["nonselected_release_blocking_obligation_count"] == 4
    for row in rows:
        assert row["modified_by_tranche_001"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_executed_in_tranche_001"


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_defines_lean_audit_surface() -> None:
    packet = _json(PACKET_PATH)
    scope = packet["execution_scope"]
    required = packet["required_evidence_surface"]
    target = packet["lean_dependency_audit_target"]
    assert scope["scope_kind"] == "LEAN_DEPENDENCY_AUDIT_CAPTURE_FOR_SELECTED_TRANCHE_ONLY"
    assert scope["selected_dependency"] == SELECTED_DEPENDENCY
    assert required["surface_kind"] == "lean_axiom_audit_readout"
    assert required["lean_target"] == LEAN_TARGET
    assert required["lean_source"] == LEAN_SOURCE
    assert required["audit_command"] == LEAN_AUDIT_COMMAND
    assert required["raw_output_required"] is True
    assert required["parsed_axioms_required"] is True
    assert required["project_axioms_used_required"] is True
    assert required["execution_status"] == "prepared_not_executed_v0"
    assert target["executed_by_this_packet"] is False


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_defines_review_requirements_and_criteria() -> None:
    packet = _json(PACKET_PATH)
    assert packet["documentation_requirement"]["required"] == (
        "conditional_after_execution_result_review"
    )
    assert packet["documentation_requirement"]["prepared_by_this_packet"] is False
    assert packet["expert_re_review_requirement"]["required"] == (
        "conditional_after_execution_result_review"
    )
    assert packet["expert_re_review_requirement"]["executed_by_this_packet"] is False
    assert len(packet["success_criteria"]) >= 5
    assert len(packet["failure_criteria"]) >= 5
    assert packet["post_packet_review_target"] == NEXT_TARGET
    assert packet["post_execution_adjudication_target"] == (
        "review_v01_alpha_dependency_remediation_tranche_002_execution_result"
    )


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_prepares_without_execution() -> None:
    packet = _json(PACKET_PATH)
    assert packet["tranche_002_execution_packet_prepared"] is True
    assert packet["execution_packet_prepared"] is True
    assert packet["remediation_execution_authorized"] is False
    assert packet["remediation_executed"] is False
    assert packet["lean_dependency_audit_executed"] is False
    assert packet["lean_dependency_evidence_captured"] is False
    assert packet["documentation_prepared"] is False
    assert packet["expert_re_review_executed"] is False


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_forbidden_effects_false() -> None:
    packet = _json(PACKET_PATH)
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


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_next_target() -> None:
    packet = _json(PACKET_PATH)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "tranche_002_execution_packet_result_review_only"
    )
    assert packet["next_action_scope"] == (
        "REVIEW_TRANCHE_002_EXECUTION_PACKET_RESULT_ONLY_NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_002_execution_packet_result": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_002": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_acceptance_and_determinism() -> None:
    packet = _json(PACKET_PATH)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_packet(
        selection_result_review_path=SELECTION_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_packet(
        selection_result_review_path=SELECTION_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_dependency_remediation_tranche_002_execution_packet_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_002_execution_packet_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_002_execution_packet_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche002ExecutionPacket" in index_text
    assert (
        "v01_dependency_remediation_tranche_002_execution_packet_does_not_execute_remediation"
        in index_text
    )
