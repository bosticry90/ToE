from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.computational_physics_integration_closeout_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
CLOSEOUT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0.json"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "computational_physics_integration_closeout_result_review_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

FORBIDDEN_TRUE_KEYS = [
    "theory_validation",
    "empirical_validation",
    "referent_comparison_execution",
    "robustness_scan_execution",
    "prediction_execution",
    "falsifier_execution",
    "theorem_discharge",
    "blocker_movement",
    "lane_reopen",
    "seam_closure",
    "phase2_authorization",
    "master_action_promotion",
    "simulation_execution",
    "validation_upgrade",
    "claim_promotion",
    "numerical_credibility_scoring",
    "external_truth_claim",
]

PROHIBITED_PHRASES = [
    "theory validation complete",
    "empirical validation complete",
    "referent comparison executed",
    "robustness scan executed",
    "prediction confirmed",
    "falsifier passed",
    "falsifier succeeded",
    "model validated",
    "claim promoted",
    "empirically supported",
    "recovered complete",
    "Phase 2 authorized",
    "seam closure authorized",
    "theorem discharged by computation",
    "master action promoted",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_computational_physics_integration_closeout_result_review_files_exist() -> None:
    assert CLOSEOUT_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_computational_physics_integration_closeout_result_review_consumes_closeout_and_accepts() -> None:
    review = _json(REVIEW_PATH)
    assert review["schema_id"] == "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["consumed_closeout"]["closeout_id"] == "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0"
    assert review["consumed_closeout"]["closeout_path"] == (
        "formal/docs/release/COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0.json"
    )
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID


def test_computational_physics_integration_closeout_result_review_acceptance_criteria() -> None:
    review = _json(REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_computational_physics_integration_closeout_result_review_scope_confirmation() -> None:
    review = _json(REVIEW_PATH)
    scope = review["scope_confirmation"]
    assert scope["stack_layer_count"] == 8
    assert scope["result_review_count"] == 8
    assert scope["row_count"] == 8
    assert scope["lineage_preserved"] is True
    assert scope["all_result_reviews_accepted"] is True
    assert scope["promotion_allowed_count"] == 0
    assert scope["validation_upgrade_count"] == 0
    assert scope["execution_claim_count"] == 0
    assert scope["completion_claim_count"] == 0
    assert scope["scoring_policy"] == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0"
    assert scope["terminal_readout"] == "NONCLAIM_CREDIBILITY_INFRASTRUCTURE_PREPARED_NO_EXECUTION_OR_PROMOTION"
    for key, value in scope["final_non_execution_readout"].items():
        assert value is True, f"Expected final non-execution readout: {key}"


def test_computational_physics_integration_closeout_result_review_forbidden_effects_false_and_no_claim_language() -> None:
    review = _json(REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = (
        json.dumps(review, sort_keys=True)
        + "\n"
        + _read(CLOSEOUT_PATH)
        + "\n"
        + _read(ROADMAP_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_computational_physics_integration_closeout_result_review_next_action_terminal() -> None:
    review = _json(REVIEW_PATH)
    assert review["next_action"] == "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    assert review["next_action_scope"] == "MAIN_TARGET_SELECTION_ONLY_NO_COMPUTATIONAL_EXECUTION_AUTHORIZATION"
    assert review["roadmap_terminal_status"] == "CLOSED_BOUNDED_NONCLAIM"


def test_computational_physics_integration_closeout_result_review_is_deterministic() -> None:
    generated_1 = build_result_review(
        closeout_path=CLOSEOUT_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        closeout_path=CLOSEOUT_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(REVIEW_PATH) == generated_1


def test_computational_physics_integration_closeout_result_review_is_pinned_and_terminal() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_STATUS_v0: CLOSED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_STATUS_v0: "
        "ACCEPTED_BOUNDED_NONCLAIM"
    ) in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0: "
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_NONCLAIM_INFRASTRUCTURE_STACK_"
        "AND_RETURNS_TO_MAIN_TARGET_SELECTION_ONLY"
    ) in roadmap_text

    for ref in (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_v0",
        "formal/docs/release/COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/computational_physics_integration_closeout_result_review_report.py",
        "formal/python/tests/test_computational_physics_integration_closeout_result_review_gate.py",
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
