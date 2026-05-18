from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_execution_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    SELECTED_DEPENDENCY,
    SELECTED_REMEDIATION_FINDING_ID,
    SELECTED_TRANCHE_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
PACKET_PATH = RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_20260515_v0.json"
RESULT_REVIEW_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_execution_packet_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationExecutionPacketResultReview.lean"
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

EXPECTED_TRACKED_IDS = [
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


def test_v01_alpha_dependency_remediation_execution_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_execution_packet_result_review_consumes_packet() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0"
    )
    assert review["review_id"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_packet"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_v0"
    assert review["consumes_packet_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_20260515_v0.json"
    )
    assert review["source_dependency_remediation_packet_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_RESULT_REVIEW_v0"
    )
    assert review["source_dependency_remediation_packet"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_PACKET_v0"
    )


def test_v01_alpha_dependency_remediation_execution_packet_result_review_tracks_all_six() -> None:
    review = _json(RESULT_REVIEW_PATH)
    tracked = review["tracked_release_blocking_findings"]
    assert review["tracked_release_blocking_finding_count"] == 6
    assert [row["dependency_finding_id"] for row in tracked] == EXPECTED_TRACKED_IDS
    assert [row["selection_status"] for row in tracked].count("selected_for_tranche_001") == 1
    assert [row["selection_status"] for row in tracked].count(
        "tracked_not_selected_for_tranche_001"
    ) == 5


def test_v01_alpha_dependency_remediation_execution_packet_result_review_selected_tranche() -> None:
    review = _json(RESULT_REVIEW_PATH)
    tranche = review["selected_tranche_review"]
    assert tranche["execution_tranche_id"] == SELECTED_TRANCHE_ID
    assert tranche["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert tranche["selected_dependency"] == SELECTED_DEPENDENCY
    assert len(tranche["required_evidence_surfaces"]) == 3
    assert tranche["lean_work_required"] is True
    assert tranche["documentation_work_required"] is True
    assert tranche["documentation_sufficient_for_remediation"] is False
    assert "expert re-review" in tranche["expert_re_review_trigger"]
    assert tranche["success_criteria_count"] >= 5
    assert tranche["failure_criteria_count"] >= 5
    assert tranche["post_execution_adjudication_target"] == (
        "review_v01_alpha_dependency_remediation_execution_result"
    )


def test_v01_alpha_dependency_remediation_execution_packet_result_review_authorizes_execution_only() -> None:
    review = _json(RESULT_REVIEW_PATH)
    routing = review["routing_decision"]
    assert routing["execution_packet_accepted"] is True
    assert routing["bounded_remediation_execution_authorized"] is True
    assert routing["authorized_tranche_id"] == SELECTED_TRANCHE_ID
    assert routing["authorized_next_target"] == NEXT_TARGET
    assert routing["release_readiness_adjudication_preparation_authorized"] is False
    assert review["bounded_remediation_execution_authorized"] is True
    assert review["remediation_execution_authorized"] is True
    assert review["remediation_executed"] is False


def test_v01_alpha_dependency_remediation_execution_packet_result_review_forbidden_effects_false() -> None:
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


def test_v01_alpha_dependency_remediation_execution_packet_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "bounded_remediation_execution_only"
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "EXECUTE_DEPENDENCY_REMEDIATION_TRANCHE_001_ONLY_NO_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "execute_v01_alpha_dependency_remediation_tranche_001": "selected",
        "execute_v01_alpha_dependency_remediation_execution_packet": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_execution_packet_result_review_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_execution_packet_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_v0",
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_execution_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_execution_packet_result_review_gate.py",
        OUTCOME_ID,
        "execute_v01_alpha_dependency_remediation_tranche_001",
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationExecutionPacketResultReview" in index_text
    assert (
        "v01_dependency_remediation_execution_packet_result_review_does_not_execute_remediation"
        in index_text
    )
