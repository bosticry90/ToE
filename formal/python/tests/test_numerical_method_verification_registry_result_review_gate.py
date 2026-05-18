from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.numerical_method_verification_registry_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT / "formal" / "python" / "tools" / "numerical_method_verification_registry_result_review_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

FORBIDDEN_TRUE_KEYS = [
    "theorem_discharge",
    "blocker_movement",
    "lane_reopen",
    "phase2_authorization",
    "empirical_validation_claim",
    "seam_closure",
    "master_action_promotion",
    "external_truth_claim",
]

PROHIBITED_PHRASES = [
    "Phase 2 authorized",
    "seam closure authorized",
    "empirical validation complete",
    "theorem discharged by computation",
    "master action promoted",
    "convergence completed",
    "MMS completed",
    "exact-solution benchmark completed",
    "solver crosscheck completed",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_numerical_method_registry_result_review_files_exist() -> None:
    assert REGISTRY_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_numerical_method_registry_result_review_consumes_registry_and_accepts() -> None:
    review = _json(REVIEW_PATH)
    assert review["schema_id"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["consumed_registry"]["registry_id"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0"
    assert (
        review["consumed_registry"]["registry_path"]
        == "formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
    )
    assert review["consumed_registry"]["registry_row_count"] == 8
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID


def test_numerical_method_registry_result_review_acceptance_criteria() -> None:
    review = _json(REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    counts = review["method_gap_confirmation"]["method_applicability_counts"]
    assert counts == {
        "comparator_or_report_surface": 5,
        "formal_or_governance_surface": 1,
        "numerical_method_applicable": 2,
    }
    assert review["scope_confirmation"]["promotion_allowed_count"] == 0
    assert review["scope_confirmation"]["all_promotion_allowed_false"] is True
    assert review["scope_confirmation"]["validation_upgrade_count"] == 0
    assert review["scope_confirmation"]["numerical_score_present"] is False
    assert review["scope_confirmation"]["method_completion_claim_count"] == 0
    assert review["scope_confirmation"]["method_completion_claims"] == []


def test_numerical_method_registry_result_review_preserves_method_gap_and_next_packet_scope() -> None:
    review = _json(REVIEW_PATH)
    assert review["method_gap_confirmation"]["primary_method_gap"] == (
        "CONVERGENCE_MMS_EXACT_SOLUTION_AND_SOLVER_CROSSCHECK_DEPTH_NOT_REGISTERED_V0"
    )
    assert review["method_gap_confirmation"]["method_verification_scope"] == (
        "REGISTER_VERIFICATION_DEPTH_ONLY_NO_COMPLETION_CLAIM"
    )
    assert review["method_gap_confirmation"]["convergence_not_registered_count"] == 2
    assert review["method_gap_confirmation"]["manufactured_solution_not_passed_count"] == 2
    assert review["method_gap_confirmation"]["solver_crosscheck_not_performed_count"] == 2
    assert review["next_packet"] == "REGIME_RECOVERY_MATRIX_v0"
    assert review["next_action"] == "PREPARE_REGIME_RECOVERY_MATRIX_AFTER_NUMERICAL_METHOD_REGISTRY_REVIEW"
    assert review["next_packet_authorization_scope"] == "PREPARATION_ONLY"


def test_numerical_method_registry_result_review_forbidden_effects_false_and_no_completion_language() -> None:
    review = _json(REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(review, sort_keys=True) + "\n" + _read(ROADMAP_PATH) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_numerical_method_registry_result_review_is_deterministic() -> None:
    generated_1 = build_result_review(registry_path=REGISTRY_PATH, captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    generated_2 = build_result_review(registry_path=REGISTRY_PATH, captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    assert generated_1 == generated_2
    assert _json(REVIEW_PATH) == generated_1


def test_numerical_method_registry_result_review_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert (
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_STATUS_v0: "
        "ACCEPTED_BOUNDED_NONCLAIM"
    ) in roadmap_text
    assert (
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_OUTCOME_v0: "
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_ACCEPTS_NONCLAIM_METHOD_DEBT_REGISTRATION_"
        "AND_AUTHORIZES_REGIME_RECOVERY_MATRIX_PREPARATION_ONLY"
    ) in roadmap_text
    assert "REGIME_RECOVERY_MATRIX_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text
    assert "REGIME_RECOVERY_MATRIX_GATE_v0: formal/python/tests/test_regime_recovery_matrix_gate.py" in roadmap_text

    for ref in (
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_v0",
        "formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/numerical_method_verification_registry_result_review_report.py",
        "formal/python/tests/test_numerical_method_verification_registry_result_review_gate.py",
        "formal/docs/release/REGIME_RECOVERY_MATRIX_20260515_v0.json",
        "formal/python/tools/regime_recovery_matrix_report.py",
        "formal/python/tests/test_regime_recovery_matrix_gate.py",
        "REGIME_RECOVERY_MATRIX_v0",
    ):
        assert ref in physics_text
