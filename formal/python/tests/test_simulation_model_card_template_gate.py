from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.simulation_model_card_template_report import (
    DEFAULT_CAPTURED_AT_UTC,
    PREPARATION_RESULT,
    REQUIRED_MODEL_CARD_FIELDS,
    TEMPLATE_ID,
    build_template,
)


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json"
REFERENT_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_20260515_v0.json"
TEMPLATE_JSON_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json"
)
TEMPLATE_MD_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "SIMULATION_MODEL_CARD_TEMPLATE_v0.md"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "simulation_model_card_template_report.py"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

FORBIDDEN_CLAIMS = [
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
    "cards instantiated",
    "model cards instantiated",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_simulation_model_card_template_files_exist() -> None:
    assert TEMPLATE_JSON_PATH.exists()
    assert TEMPLATE_MD_PATH.exists()
    assert TOOL_PATH.exists()


def test_simulation_model_card_template_top_level_contract() -> None:
    template = _json(TEMPLATE_JSON_PATH)
    assert template["schema_id"] == "SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0"
    assert template["template_id"] == TEMPLATE_ID
    assert template["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert template["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert template["authorization_class"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert template["preparation_result"] == PREPARATION_RESULT
    assert template["consumes_result_review"] == "REFERENT_REGISTRY_RESULT_REVIEW_v0"
    assert template["source_referent_registry"] == "REFERENT_REGISTRY_v0"
    assert template["source_referent_registry_row_count"] == 8
    assert template["template_scope"] == "DEFINE_MODEL_CARD_TEMPLATE_ONLY_NO_CARD_INSTANTIATION_CLAIM"
    assert template["template_claim_ceiling"] == "model_documentation_template_only"


def test_simulation_model_card_template_does_not_instantiate_cards_or_promote() -> None:
    template = _json(TEMPLATE_JSON_PATH)
    assert template["instantiated_model_card_count"] == 0
    assert template["model_card_instantiation_claim_count"] == 0
    assert template["promotion_allowed_default"] is False
    assert template["card_defaults"]["promotion_allowed"] is False
    assert template["card_defaults"]["validation_upgrade_from_template"] is False
    assert template["card_defaults"]["comparison_execution_status"] == "not_executed_by_template"


def test_simulation_model_card_template_includes_all_required_fields_and_claim_controls() -> None:
    template = _json(TEMPLATE_JSON_PATH)
    assert template["required_model_card_fields"] == REQUIRED_MODEL_CARD_FIELDS
    for field in REQUIRED_MODEL_CARD_FIELDS:
        assert f"`{field}`" in _read(TEMPLATE_MD_PATH)
    assert sorted(template["forbidden_claims"]) == sorted(FORBIDDEN_CLAIMS)
    assert "promotion_allowed" in template["required_model_card_fields"]
    assert "forbidden_claims" in template["required_model_card_fields"]
    assert "claim_ceiling" in template["required_model_card_fields"]


def test_simulation_model_card_template_handles_numerical_and_non_applicable_artifacts() -> None:
    template = _json(TEMPLATE_JSON_PATH)
    rules_by_class = {rule["artifact_class"]: rule for rule in template["artifact_class_rules"]}
    numerical = rules_by_class["simulation_or_numerical_method_surface"]
    assert numerical["method_documentation_requirement"] == "require_numerical_method_details"
    assert numerical["non_applicability_reason_required"] is False
    assert "equation_or_system_solved" in numerical["required_method_fields"]
    assert "solver_crosscheck_status" in numerical["required_method_fields"]

    for artifact_class in (
        "comparator_or_report_surface",
        "formal_governance_surface",
        "seam_or_mismatch_report_surface",
    ):
        rule = rules_by_class[artifact_class]
        assert rule["method_documentation_requirement"] == "require_not_applicable_reason"
        assert rule["non_applicability_reason_required"] is True
        assert rule["required_method_fields"] == []
    assert "numerical_method_or_not_applicable_reason" in template["non_applicability_handling"]


def test_simulation_model_card_template_preserves_lineage_context_without_execution() -> None:
    template = _json(TEMPLATE_JSON_PATH)
    context = template["lineage_context"]
    assert context["referent_row_count"] == 8
    assert context["source_method_applicability_counts"] == {
        "comparator_or_report_surface": 5,
        "formal_or_governance_surface": 1,
        "numerical_method_applicable": 2,
    }
    assert context["comparison_execution_status_counts"] == {"not_executed_v0": 8}
    assert context["uq_dependency_counts"] == {
        "uq_not_quantified": 5,
        "uq_partial_quantitative": 1,
        "uq_qualitative": 2,
    }
    assert template["next_recommended_action"] == "REVIEW_SIMULATION_MODEL_CARD_TEMPLATE_RESULT"


def test_simulation_model_card_template_forbidden_effects_and_language() -> None:
    template_text = json.dumps(_json(TEMPLATE_JSON_PATH), sort_keys=True) + "\n" + _read(TEMPLATE_MD_PATH)
    for claim in FORBIDDEN_CLAIMS:
        assert claim in template_text
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in template_text


def test_simulation_model_card_template_is_deterministic() -> None:
    generated_1 = build_template(
        review_path=REVIEW_PATH,
        referent_registry_path=REFERENT_REGISTRY_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_template(
        review_path=REVIEW_PATH,
        referent_registry_path=REFERENT_REGISTRY_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(TEMPLATE_JSON_PATH) == generated_1


def test_simulation_model_card_template_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert "SIMULATION_MODEL_CARD_TEMPLATE_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert (
        "SIMULATION_MODEL_CARD_TEMPLATE_OUTCOME_v0: "
        "SIMULATION_MODEL_CARD_TEMPLATE_PREPARED_FROM_REFERENT_REGISTRY_REVIEW_"
        "WITH_NONCLAIM_MODEL_DOCUMENTATION_CEILINGS"
    ) in roadmap_text

    for ref in (
        "SIMULATION_MODEL_CARD_TEMPLATE_v0",
        "formal/docs/release/SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json",
        "formal/docs/paper/SIMULATION_MODEL_CARD_TEMPLATE_v0.md",
        "formal/python/tools/simulation_model_card_template_report.py",
        "formal/python/tests/test_simulation_model_card_template_gate.py",
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
