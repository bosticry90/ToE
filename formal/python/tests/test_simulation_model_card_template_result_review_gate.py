from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.simulation_model_card_template_report import REQUIRED_MODEL_CARD_FIELDS
from formal.python.tools.simulation_model_card_template_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TEMPLATE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json"
REFERENT_REVIEW_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT / "formal" / "python" / "tools" / "simulation_model_card_template_result_review_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

FORBIDDEN_TRUE_KEYS = [
    "simulation_execution",
    "referent_comparison_execution",
    "robustness_scan_execution",
    "validation_upgrade",
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
    "model cards instantiated",
    "simulation executed",
    "referent comparison executed",
    "robustness scan executed",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_simulation_model_card_template_result_review_files_exist() -> None:
    assert TEMPLATE_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_simulation_model_card_template_result_review_consumes_template_and_accepts() -> None:
    review = _json(REVIEW_PATH)
    assert review["schema_id"] == "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["consumed_template"]["template_id"] == "SIMULATION_MODEL_CARD_TEMPLATE_v0"
    assert review["consumed_template"]["template_path"] == (
        "formal/docs/release/SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json"
    )
    assert review["source_lineage"]["source_referent_registry_result_review"] == (
        "REFERENT_REGISTRY_RESULT_REVIEW_v0"
    )
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID


def test_simulation_model_card_template_result_review_acceptance_criteria() -> None:
    review = _json(REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_simulation_model_card_template_result_review_preserves_zero_instantiation_and_defaults() -> None:
    review = _json(REVIEW_PATH)
    scope = review["scope_confirmation"]
    assert scope["instantiated_model_card_count"] == 0
    assert scope["model_card_instantiation_claim_count"] == 0
    assert scope["promotion_allowed_default"] is False
    assert scope["card_default_promotion_allowed"] is False
    assert scope["card_default_validation_upgrade_from_template"] is False


def test_simulation_model_card_template_result_review_confirms_fields_and_applicability_rules() -> None:
    review = _json(REVIEW_PATH)
    confirmation = review["template_confirmation"]
    assert confirmation["required_model_card_fields"] == REQUIRED_MODEL_CARD_FIELDS
    assert confirmation["required_field_count"] == len(REQUIRED_MODEL_CARD_FIELDS)
    assert confirmation["artifact_class_rule_count"] == 4
    assert confirmation["numerical_and_non_numerical_handling_present"] is True
    assert confirmation["template_claim_ceiling"] == "model_documentation_template_only"
    assert confirmation["template_scope"] == "DEFINE_MODEL_CARD_TEMPLATE_ONLY_NO_CARD_INSTANTIATION_CLAIM"
    assert confirmation["lineage_context"]["referent_row_count"] == 8
    assert confirmation["lineage_context"]["source_method_applicability_counts"] == {
        "comparator_or_report_surface": 5,
        "formal_or_governance_surface": 1,
        "numerical_method_applicable": 2,
    }


def test_simulation_model_card_template_result_review_forbidden_effects_false_and_no_execution_language() -> None:
    review = _json(REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(review, sort_keys=True) + "\n" + _read(ROADMAP_PATH) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_simulation_model_card_template_result_review_next_packet_scope() -> None:
    review = _json(REVIEW_PATH)
    assert review["next_packet"] == "PREDICTION_AND_FALSIFIER_REGISTRY_v0"
    assert review["next_action"] == "PREPARE_PREDICTION_AND_FALSIFIER_REGISTRY_AFTER_MODEL_CARD_TEMPLATE_REVIEW"
    assert review["next_packet_authorization_scope"] == "PREPARATION_ONLY"


def test_simulation_model_card_template_result_review_is_deterministic() -> None:
    generated_1 = build_result_review(
        template_path=TEMPLATE_PATH,
        referent_review_path=REFERENT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        template_path=TEMPLATE_PATH,
        referent_review_path=REFERENT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(REVIEW_PATH) == generated_1


def test_simulation_model_card_template_result_review_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_OUTCOME_v0: "
        "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_ACCEPTS_NONCLAIM_MODEL_DOCUMENTATION_TEMPLATE_"
        "AND_AUTHORIZES_PREDICTION_AND_FALSIFIER_REGISTRY_PREPARATION_ONLY"
    ) in roadmap_text
    assert "PREDICTION_AND_FALSIFIER_REGISTRY_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text

    for ref in (
        "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_v0",
        "formal/docs/release/SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/simulation_model_card_template_result_review_report.py",
        "formal/python/tests/test_simulation_model_card_template_result_review_gate.py",
        "PREDICTION_AND_FALSIFIER_REGISTRY_v0",
        "PREPARE_PREDICTION_AND_FALSIFIER_REGISTRY_AFTER_MODEL_CARD_TEMPLATE_REVIEW",
    ):
        assert ref in physics_text
