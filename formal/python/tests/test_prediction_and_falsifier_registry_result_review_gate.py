from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prediction_and_falsifier_registry_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "prediction_and_falsifier_registry_result_review_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

EXPECTED_ROWS = [
    "C6_CP_NLSE_2D_LANE",
    "C7_MT01A_ACOUSTIC_METRIC_LANE",
    "UCFF_SPECTRAL_AUDIT_LINEAGE",
    "BRAGG_DISPERSION_ELIMINATIVE_LANE",
    "RL01_RELATIVISTIC_DISPERSION_LIMIT",
    "RL02_NONRELATIVISTIC_NLSE_LIMIT",
    "GR01_DERIVATION_COMPLETENESS_GATE",
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS",
]

FORBIDDEN_TRUE_KEYS = [
    "prediction_confirmation",
    "prediction_execution",
    "falsifier_execution",
    "falsifier_success_claim",
    "validation_upgrade",
    "recovery_claim",
    "empirical_support_claim",
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


def _ids(payload: dict, key: str) -> list[str]:
    return [row["artifact_id"] for row in payload[key]]


def test_prediction_and_falsifier_registry_result_review_files_exist() -> None:
    assert REGISTRY_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_prediction_and_falsifier_registry_result_review_consumes_registry_and_accepts() -> None:
    review = _json(REVIEW_PATH)
    assert review["schema_id"] == "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["consumed_registry"]["registry_id"] == "PREDICTION_AND_FALSIFIER_REGISTRY_v0"
    assert review["consumed_registry"]["registry_path"] == (
        "formal/docs/release/PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json"
    )
    assert review["source_lineage"]["source_model_card_template_result_review"] == (
        "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_v0"
    )
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID


def test_prediction_and_falsifier_registry_result_review_acceptance_criteria() -> None:
    review = _json(REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_prediction_and_falsifier_registry_result_review_preserves_lineage_and_nonexecution() -> None:
    registry = _json(REGISTRY_PATH)
    review = _json(REVIEW_PATH)
    scope = review["scope_confirmation"]
    assert _ids(registry, "registry_rows") == EXPECTED_ROWS
    assert scope["row_count"] == 8
    assert scope["promotion_allowed_count"] == 0
    assert scope["validation_upgrade_count"] == 0
    assert scope["prediction_execution_claim_count"] == 0
    assert scope["falsifier_execution_claim_count"] == 0
    assert scope["prediction_result_claim_count"] == 0
    assert scope["falsifier_result_claim_count"] == 0
    assert scope["execution_status_counts"] == {"not_executed_v0": 8}
    assert scope["prediction_status_counts"] == {"candidate_not_executed_v0": 8}
    assert scope["falsifier_status_counts"] == {"defined_not_executed_v0": 8}
    for row in registry["registry_rows"]:
        assert row["execution_status"] == "not_executed_v0"
        assert row["prediction_execution_claim"] is False
        assert row["falsifier_execution_claim"] is False
        assert row["prediction_result_claim"] is False
        assert row["falsifier_result_claim"] is False
        assert row["promotion_allowed"] is False


def test_prediction_and_falsifier_registry_result_review_keeps_dependencies_visible() -> None:
    review = _json(REVIEW_PATH)
    scope = review["scope_confirmation"]
    assert scope["method_verification_dependency_counts"] == {
        "method_debt_visible": 2,
        "method_verification_not_applicable_comparator_surface": 3,
        "method_verification_not_applicable_formal_governance_surface": 1,
        "method_verification_not_applicable_report_surface": 2,
    }
    assert scope["uq_dependency_counts"] == {
        "uq_not_quantified": 5,
        "uq_partial_quantitative": 1,
        "uq_qualitative": 2,
    }
    assert scope["robustness_dependency_counts"] == {"robustness_protocol_not_executed": 8}
    assert scope["referent_dependency_counts"] == {
        "blocked_pending_governance_resolution": 1,
        "candidate_not_registered_as_validation": 7,
    }
    assert scope["primary_falsifier_gap"] == (
        "PREDICTION_AND_FALSIFIER_PASS_FAIL_CRITERIA_REGISTERED_BUT_NOT_EXECUTED_V0"
    )
    assert scope["registry_scope"] == "REGISTER_TEST_DESIGNS_ONLY_NO_EXECUTION_OR_RESULT_CLAIM"


def test_prediction_and_falsifier_registry_result_review_forbidden_effects_false_and_no_result_language() -> None:
    review = _json(REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = (
        json.dumps(review, sort_keys=True)
        + "\n"
        + _read(REGISTRY_PATH)
        + "\n"
        + _read(ROADMAP_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_prediction_and_falsifier_registry_result_review_next_packet_scope() -> None:
    review = _json(REVIEW_PATH)
    assert review["next_packet"] == "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0"
    assert review["next_action"] == (
        "PREPARE_COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_AFTER_PREDICTION_AND_FALSIFIER_REGISTRY_REVIEW"
    )
    assert review["next_packet_authorization_scope"] == "PREPARATION_ONLY"


def test_prediction_and_falsifier_registry_result_review_is_deterministic() -> None:
    generated_1 = build_result_review(
        registry_path=REGISTRY_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        registry_path=REGISTRY_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(REVIEW_PATH) == generated_1


def test_prediction_and_falsifier_registry_result_review_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_OUTCOME_v0: "
        "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_ACCEPTS_NONCLAIM_TEST_DESIGN_REGISTRATION_"
        "AND_AUTHORIZES_COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_PREPARATION_ONLY"
    ) in roadmap_text
    assert "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_STATUS_v0: CLOSED_BOUNDED_NONCLAIM" in roadmap_text

    for ref in (
        "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_v0",
        "formal/docs/release/PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/prediction_and_falsifier_registry_result_review_report.py",
        "formal/python/tests/test_prediction_and_falsifier_registry_result_review_gate.py",
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0",
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
