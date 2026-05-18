from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.simulation_model_card_template_report import (
    FORBIDDEN_CLAIMS,
    REQUIRED_MODEL_CARD_FIELDS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_ACCEPTS_NONCLAIM_MODEL_DOCUMENTATION_TEMPLATE_"
    "AND_AUTHORIZES_PREDICTION_AND_FALSIFIER_REGISTRY_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_TEMPLATE_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json"
)
DEFAULT_REFERENT_REVIEW_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0.json"
)

FORBIDDEN_EFFECTS = [
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


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _rules_by_class(template: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(rule["artifact_class"]): rule for rule in template.get("artifact_class_rules", [])}


def _handles_numerical_and_non_numerical(template: dict[str, Any]) -> bool:
    rules = _rules_by_class(template)
    numerical = rules.get("simulation_or_numerical_method_surface")
    if not numerical:
        return False
    if numerical.get("method_documentation_requirement") != "require_numerical_method_details":
        return False
    if numerical.get("non_applicability_reason_required") is not False:
        return False
    required_method_fields = set(numerical.get("required_method_fields", []))
    if not {"equation_or_system_solved", "solver_crosscheck_status"}.issubset(required_method_fields):
        return False

    for artifact_class in (
        "comparator_or_report_surface",
        "formal_governance_surface",
        "seam_or_mismatch_report_surface",
    ):
        rule = rules.get(artifact_class)
        if not rule:
            return False
        if rule.get("method_documentation_requirement") != "require_not_applicable_reason":
            return False
        if rule.get("non_applicability_reason_required") is not True:
            return False
        if rule.get("required_method_fields") != []:
            return False
    return "numerical_method_or_not_applicable_reason" in str(template.get("non_applicability_handling", ""))


def build_result_review(
    *,
    template_path: Path = DEFAULT_TEMPLATE_PATH,
    referent_review_path: Path = DEFAULT_REFERENT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    template = _read_json(template_path)
    referent_review = _read_json(referent_review_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    required_fields_present = template.get("required_model_card_fields") == REQUIRED_MODEL_CARD_FIELDS
    forbidden_claims_present = sorted(template.get("forbidden_claims", [])) == sorted(FORBIDDEN_CLAIMS)

    acceptance_criteria = {
        "consumes_simulation_model_card_template": template.get("template_id")
        == "SIMULATION_MODEL_CARD_TEMPLATE_v0",
        "template_status_nonclaim": template.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "authorization_class_preserved": template.get("authorization_class")
        == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "consumes_referent_registry_result_review": template.get("consumes_result_review")
        == "REFERENT_REGISTRY_RESULT_REVIEW_v0",
        "source_referent_review_accepted": referent_review.get("accepted") is True,
        "source_referent_review_authorized_template_only": referent_review.get("next_packet")
        == "SIMULATION_MODEL_CARD_TEMPLATE_v0",
        "template_scope_only": template.get("template_scope")
        == "DEFINE_MODEL_CARD_TEMPLATE_ONLY_NO_CARD_INSTANTIATION_CLAIM",
        "instantiated_model_card_count_zero": int(template.get("instantiated_model_card_count", -1)) == 0,
        "model_card_instantiation_claim_count_zero": int(
            template.get("model_card_instantiation_claim_count", -1)
        )
        == 0,
        "required_model_card_fields_present": required_fields_present,
        "promotion_allowed_default_false": template.get("promotion_allowed_default") is False,
        "card_default_promotion_allowed_false": template.get("card_defaults", {}).get("promotion_allowed") is False,
        "card_default_validation_upgrade_false": template.get("card_defaults", {}).get(
            "validation_upgrade_from_template"
        )
        is False,
        "forbidden_claim_fields_present": forbidden_claims_present,
        "numerical_and_non_numerical_handling_present": _handles_numerical_and_non_numerical(template),
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }

    accepted = all(acceptance_criteria.values())
    if accepted:
        next_packet = "PREDICTION_AND_FALSIFIER_REGISTRY_v0"
        next_action = "PREPARE_PREDICTION_AND_FALSIFIER_REGISTRY_AFTER_MODEL_CARD_TEMPLATE_REVIEW"
        outcome_id = OUTCOME_ID
    else:
        next_packet = "BLOCKED_PENDING_SIMULATION_MODEL_CARD_TEMPLATE_REMEDIATION"
        next_action = "REMEDIATE_SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_FAILURE"
        outcome_id = "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_BLOCKED"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_template": {
            "template_id": template.get("template_id"),
            "template_path": _ptr(template_path),
            "template_schema_id": template.get("schema_id"),
            "template_preparation_result": template.get("preparation_result"),
        },
        "source_lineage": {
            "source_referent_registry_result_review": referent_review.get("review_id"),
            "source_referent_registry_result_review_path": _ptr(referent_review_path),
            "source_referent_review_accepted": referent_review.get("accepted") is True,
        },
        "acceptance_criteria": acceptance_criteria,
        "accepted": accepted,
        "outcome_id": outcome_id,
        "forbidden_effect_status": forbidden_effect_status,
        "scope_confirmation": {
            "instantiated_model_card_count": int(template.get("instantiated_model_card_count", -1)),
            "model_card_instantiation_claim_count": int(
                template.get("model_card_instantiation_claim_count", -1)
            ),
            "promotion_allowed_default": bool(template.get("promotion_allowed_default", True)),
            "card_default_promotion_allowed": bool(template.get("card_defaults", {}).get("promotion_allowed", True)),
            "card_default_validation_upgrade_from_template": bool(
                template.get("card_defaults", {}).get("validation_upgrade_from_template", True)
            ),
        },
        "template_confirmation": {
            "required_model_card_fields": template.get("required_model_card_fields", []),
            "required_field_count": len(template.get("required_model_card_fields", [])),
            "forbidden_claims": template.get("forbidden_claims", []),
            "artifact_class_rule_count": len(template.get("artifact_class_rules", [])),
            "numerical_and_non_numerical_handling_present": _handles_numerical_and_non_numerical(template),
            "template_claim_ceiling": template.get("template_claim_ceiling"),
            "template_scope": template.get("template_scope"),
            "lineage_context": template.get("lineage_context", {}),
        },
        "next_packet": next_packet,
        "next_action": next_action,
        "next_packet_authorization_scope": "PREPARATION_ONLY",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Result review accepts nonclaim model-documentation template bookkeeping only; it authorizes "
            "prediction and falsifier registry preparation only and does not authorize model-card instantiation, "
            "simulation execution, referent comparison execution, robustness scan execution, validation upgrade, "
            "theorem discharge, seam closure, Phase 2 authorization, master-action promotion, or external-truth claim."
        ),
    }


def write_result_review(
    *,
    template_path: Path = DEFAULT_TEMPLATE_PATH,
    referent_review_path: Path = DEFAULT_REFERENT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        template_path=template_path,
        referent_review_path=referent_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the simulation model-card template result review.")
    parser.add_argument("--template", type=Path, default=DEFAULT_TEMPLATE_PATH)
    parser.add_argument("--referent-review", type=Path, default=DEFAULT_REFERENT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    template_path = ns.template if ns.template.is_absolute() else (REPO_ROOT / ns.template)
    referent_review_path = (
        ns.referent_review if ns.referent_review.is_absolute() else (REPO_ROOT / ns.referent_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        template_path=template_path,
        referent_review_path=referent_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "simulation_model_card_template_result_review_report: "
        f"accepted={payload['accepted']} next_packet={payload['next_packet']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
