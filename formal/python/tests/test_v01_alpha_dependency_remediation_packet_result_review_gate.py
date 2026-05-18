from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
PACKET_PATH = RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_20260515_v0.json"
RESULT_REVIEW_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_packet_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationPacketResultReview.lean"
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

EXPECTED_DEPENDENCY_IDS = [
    "V01-ALPHA-DEP-REM-001",
    "V01-ALPHA-DEP-REM-002",
    "V01-ALPHA-DEP-REM-003",
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
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


def test_v01_alpha_dependency_remediation_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_packet_result_review_consumes_packet() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_packet"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_v0"
    assert review["consumes_packet_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_20260515_v0.json"
    )
    assert review["source_expert_review_execution_result_review"] == (
        "V01_ALPHA_EXPERT_REVIEW_EXECUTION_RESULT_REVIEW_v0"
    )
    assert review["source_expert_review_execution"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_v0"


def test_v01_alpha_dependency_remediation_packet_result_review_accepts_planning_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_ONLY_NO_REMEDIATION_EXECUTION"
    )
    assert review["packet_acceptance_posture"] == "remediation_plan_accepted_as_planning_only"
    summary = review["remediation_plan_review_summary"]
    assert summary["release_blocking_findings_present"] == 6
    assert summary["dependency_finding_ids"] == EXPECTED_DEPENDENCY_IDS
    assert summary["dependency_classes"] == [
        "blocked_bridge_authorization_dependency",
        "lean_bridge_dependency",
        "lean_theorem_dependency",
    ]
    assert summary["lean_work_required_count"] == 6
    assert summary["documentation_sufficient_count"] == 0
    assert summary["expert_re_review_required_count"] == 6
    assert summary["release_readiness_reconsiderable_after_remediation_count"] == 6
    assert summary["remediation_execution_count"] == 0
    assert summary["remediation_result_count"] == 0


def test_v01_alpha_dependency_remediation_packet_result_review_rows_complete() -> None:
    review = _json(RESULT_REVIEW_PATH)
    rows = review["reviewed_remediation_rows"]
    assert len(rows) == 6
    assert [row["dependency_finding_id"] for row in rows] == EXPECTED_DEPENDENCY_IDS
    for row in rows:
        assert row["dependency"]
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
        assert row["next_bounded_action"].startswith("prepare_remediation_tranche_for_")
        assert row["remediation_execution_status"] == "not_executed_v0"


def test_v01_alpha_dependency_remediation_packet_result_review_authorizes_packet_preparation_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    routing = review["routing_decision"]
    assert routing["remediation_plan_accepted"] is True
    assert routing["one_bounded_remediation_execution_packet_preparation_authorized"] is True
    assert routing["remediation_execution_authorized"] is False
    assert routing["release_readiness_adjudication_preparation_authorized"] is False
    assert review["remediation_execution_packet_preparation_authorized"] is True
    assert review["remediation_execution_authorized"] is False
    assert review["remediation_executed"] is False


def test_v01_alpha_dependency_remediation_packet_result_review_forbidden_effects_false() -> None:
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

    combined = json.dumps(review, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_dependency_remediation_packet_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "bounded_remediation_execution_packet_preparation_only"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_ONE_BOUNDED_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_ONLY_"
        "NO_REMEDIATION_EXECUTION_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_dependency_remediation_execution_packet": "selected",
        "execute_v01_alpha_dependency_remediation_tranche": "deferred",
        "prepare_v01_alpha_dependency_remediation_priority_split_packet": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_packet_result_review_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_packet_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_v0",
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_packet_result_review_gate.py",
        OUTCOME_ID,
        "prepare_v01_alpha_dependency_remediation_execution_packet",
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationPacketResultReview" in index_text
    assert (
        "v01_dependency_remediation_packet_result_review_does_not_execute_remediation"
        in index_text
    )
