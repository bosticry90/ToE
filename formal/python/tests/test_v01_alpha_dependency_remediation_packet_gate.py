from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    build_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_20260515_v0.json"
)
PACKET_PATH = RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_20260515_v0.json"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "v01_alpha_dependency_remediation_packet_report.py"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationPacket.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "dependency_remediation_executed",
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

EXPECTED_DEPENDENCIES = [
    "master_action_stationary_implies_free_scalar_kg",
    "stationary_implies_operator_zero",
    "finite_transport_theorems_construct_residual_package_v0",
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0",
    "supplied_interface_alignment_semantics_construct_bridge_package_v0",
    "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0",
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


def test_v01_alpha_dependency_remediation_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert PACKET_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_packet_consumes_result_review() -> None:
    packet = _json(PACKET_PATH)
    assert packet["schema_id"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_20260515_v0"
    assert packet["packet_id"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_v0"
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_result_review"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_v0"
    assert packet["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_20260515_v0.json"
    )
    assert packet["source_expert_review_execution"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_v0"


def test_v01_alpha_dependency_remediation_packet_preserves_six_blockers() -> None:
    packet = _json(PACKET_PATH)
    rows = packet["release_blocking_findings_preserved"]
    assert packet["release_blocking_finding_count"] == 6
    assert [row["dependency"] for row in rows] == EXPECTED_DEPENDENCIES
    assert [row["dependency_finding_id"] for row in rows] == [
        "V01-ALPHA-DEP-REM-001",
        "V01-ALPHA-DEP-REM-002",
        "V01-ALPHA-DEP-REM-003",
        "V01-ALPHA-DEP-REM-004",
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    for row in rows:
        assert row["blocks_v01_alpha_release_packet"] is True
        assert row["requires_remediation_before_release_assembly"] is True
        assert row["proof_debt_discharge_claim"] is False


def test_v01_alpha_dependency_remediation_packet_defines_row_remediation_plan() -> None:
    packet = _json(PACKET_PATH)
    rows = packet["release_blocking_findings_preserved"]
    assert {row["release_dependency_class"] for row in rows} == {"release_blocking_pending_capture"}
    assert {row["release_label"] for row in rows} == {"T-LEAN-COND", "B-BLOCKED"}
    for row in rows:
        assert row["dependency_class"] in {
            "lean_theorem_dependency",
            "lean_bridge_dependency",
            "blocked_bridge_authorization_dependency",
        }
        assert row["blocking_reason"]
        assert row["required_remediation_type"] in {
            "exact_lean_dependency_and_proof_debt_adjudication",
            "source_map_authorization_and_dependency_adjudication",
        }
        assert len(row["required_evidence_surface"]) == 3
        assert row["lean_work_required"] is True
        assert row["documentation_sufficient"] is False
        assert row["expert_re_review_required"] is True
        assert row["release_readiness_can_be_reconsidered_after_remediation"] is True
        assert row["next_bounded_action"].startswith("prepare_remediation_tranche_for_")
        assert row["remediation_execution_status"] == "not_executed_v0"
        assert row["remediation_result_status"] == "not_produced_v0"


def test_v01_alpha_dependency_remediation_packet_prepares_only() -> None:
    packet = _json(PACKET_PATH)
    assert packet["packet_scope"] == "PREPARE_DEPENDENCY_REMEDIATION_PACKET_ONLY_NO_REMEDIATION_EXECUTION"
    assert packet["remediation_plan_status"] == "prepared_not_executed"
    summary = packet["remediation_plan_summary"]
    assert summary["release_blocking_findings_targeted"] == 6
    assert summary["lean_work_required_count"] == 6
    assert summary["documentation_sufficient_count"] == 0
    assert summary["expert_re_review_required_count"] == 6
    assert summary["release_readiness_reconsiderable_after_remediation_count"] == 6
    assert summary["remediation_execution_count"] == 0
    assert summary["remediation_result_count"] == 0
    assert packet["remediation_execution_authorized"] is False
    assert packet["remediation_executed"] is False


def test_v01_alpha_dependency_remediation_packet_forbidden_effects_false() -> None:
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

    combined = json.dumps(packet, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_dependency_remediation_packet_next_target() -> None:
    packet = _json(PACKET_PATH)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == "result_review_only"
    assert packet["selection_count"] == 1
    assert packet["next_action_scope"] == (
        "REVIEW_DEPENDENCY_REMEDIATION_PACKET_RESULT_ONLY_NO_REMEDIATION_EXECUTION"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_packet_result": "selected",
        "execute_v01_alpha_dependency_remediation_tranche": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_packet_acceptance_and_determinism() -> None:
    packet = _json(PACKET_PATH)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_dependency_remediation_packet_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_v0",
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_packet_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_packet_gate.py",
        OUTCOME_ID,
        "review_v01_alpha_dependency_remediation_packet_result",
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationPacket" in index_text
    assert "v01_dependency_remediation_packet_does_not_execute_remediation" in index_text
