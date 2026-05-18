from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0"
TEMPLATE_ID = "SIMULATION_MODEL_CARD_TEMPLATE_v0"
PREPARATION_RESULT = (
    "SIMULATION_MODEL_CARD_TEMPLATE_PREPARED_FROM_REFERENT_REGISTRY_REVIEW_"
    "WITH_NONCLAIM_MODEL_DOCUMENTATION_CEILINGS"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_REVIEW_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json"
DEFAULT_REFERENT_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_20260515_v0.json"
DEFAULT_JSON_OUT = (
    REPO_ROOT / "formal" / "docs" / "release" / "SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json"
)
DEFAULT_MD_OUT = REPO_ROOT / "formal" / "docs" / "paper" / "SIMULATION_MODEL_CARD_TEMPLATE_v0.md"

REQUIRED_MODEL_CARD_FIELDS = [
    "model_id",
    "artifact_id",
    "source_path",
    "model_family",
    "purpose",
    "governing_equations_or_report_logic",
    "assumptions",
    "inputs",
    "outputs",
    "numerical_method_or_not_applicable_reason",
    "verification_status",
    "validation_status",
    "known_limit_or_referent_status",
    "uq_status",
    "robustness_status",
    "sensitivity_protocol_status",
    "failure_modes",
    "claim_ceiling",
    "promotion_allowed",
    "forbidden_claims",
    "upgrade_requirements",
]

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

ARTIFACT_CLASS_RULES = [
    {
        "artifact_class": "simulation_or_numerical_method_surface",
        "method_documentation_requirement": "require_numerical_method_details",
        "required_method_fields": [
            "equation_or_system_solved",
            "discretization_family",
            "time_integrator",
            "spatial_operator",
            "convergence_status",
            "benchmark_status",
            "stability_condition_status",
            "solver_crosscheck_status",
        ],
        "non_applicability_reason_required": False,
    },
    {
        "artifact_class": "comparator_or_report_surface",
        "method_documentation_requirement": "require_not_applicable_reason",
        "required_method_fields": [],
        "non_applicability_reason_required": True,
    },
    {
        "artifact_class": "formal_governance_surface",
        "method_documentation_requirement": "require_not_applicable_reason",
        "required_method_fields": [],
        "non_applicability_reason_required": True,
    },
    {
        "artifact_class": "seam_or_mismatch_report_surface",
        "method_documentation_requirement": "require_not_applicable_reason",
        "required_method_fields": [],
        "non_applicability_reason_required": True,
    },
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        value = str(row.get(field, "missing"))
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def build_template(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    referent_registry_path: Path = DEFAULT_REFERENT_REGISTRY_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    referent_registry = _read_json(referent_registry_path)
    rows = list(referent_registry.get("referent_rows", []))
    if review.get("accepted") is not True:
        raise ValueError("Cannot prepare model-card template from an unaccepted referent-registry result review.")
    if review.get("next_packet") != TEMPLATE_ID:
        raise ValueError("Referent-registry result review did not authorize model-card template preparation.")
    if review.get("next_packet_authorization_scope") != "PREPARATION_ONLY":
        raise ValueError("Referent-registry result review did not restrict template work to preparation only.")

    return {
        "schema_id": SCHEMA_ID,
        "template_id": TEMPLATE_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "preparation_result": PREPARATION_RESULT,
        "consumes_result_review": "REFERENT_REGISTRY_RESULT_REVIEW_v0",
        "consumes_result_review_pointer": _ptr(review_path),
        "source_referent_registry": "REFERENT_REGISTRY_v0",
        "source_referent_registry_pointer": _ptr(referent_registry_path),
        "source_referent_registry_row_count": int(referent_registry.get("row_count", -1)),
        "template_scope": "DEFINE_MODEL_CARD_TEMPLATE_ONLY_NO_CARD_INSTANTIATION_CLAIM",
        "instantiated_model_card_count": 0,
        "model_card_instantiation_claim_count": 0,
        "promotion_allowed_default": False,
        "template_claim_ceiling": "model_documentation_template_only",
        "required_model_card_fields": REQUIRED_MODEL_CARD_FIELDS,
        "forbidden_claims": FORBIDDEN_CLAIMS,
        "artifact_class_rules": ARTIFACT_CLASS_RULES,
        "non_applicability_handling": (
            "Non-simulation, comparator/report, seam/mismatch, and formal/governance cards must populate "
            "numerical_method_or_not_applicable_reason with an explicit reason instead of fabricating solver details."
        ),
        "card_defaults": {
            "promotion_allowed": False,
            "claim_ceiling": "model_card_reviewability_only",
            "comparison_execution_status": "not_executed_by_template",
            "validation_upgrade_from_template": False,
        },
        "lineage_context": {
            "referent_row_count": len(rows),
            "source_method_applicability_counts": _counts(rows, "source_method_applicability"),
            "validation_status_counts": _counts(rows, "validation_status"),
            "uq_dependency_counts": _counts(rows, "uq_dependency"),
            "comparison_execution_status_counts": _counts(rows, "comparison_execution_status"),
        },
        "next_recommended_action": "REVIEW_SIMULATION_MODEL_CARD_TEMPLATE_RESULT",
        "non_claim_boundary": (
            "Simulation model card template only; defines required documentation fields and applicability rules "
            "without instantiating model cards, executing simulations, executing comparisons, upgrading validation, "
            "discharging theorem debt, moving blockers, reopening lanes, authorizing Phase 2, claiming empirical "
            "validation, closing seams, promoting the master action, or making external-truth claims."
        ),
    }


def build_markdown_template(template: dict[str, Any]) -> str:
    lines = [
        "# Simulation Model Card Template v0",
        "",
        "Spec ID:",
        "- `SIMULATION_MODEL_CARD_TEMPLATE_v0`",
        "",
        "Preparation result:",
        f"- `{template['preparation_result']}`",
        "",
        "Authority binding:",
        f"- `{template['authorization_class']}`",
        f"- Consumed result review: `{template['consumes_result_review_pointer']}`",
        f"- Source referent registry: `{template['source_referent_registry_pointer']}`",
        "- JSON template: `formal/docs/release/SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json`",
        "- Gate: `formal/python/tests/test_simulation_model_card_template_gate.py`",
        "",
        "Non-claim boundary:",
        f"- {template['non_claim_boundary']}",
        "",
        "Template scope:",
        f"- `{template['template_scope']}`",
        f"- Instantiated model card count: `{template['instantiated_model_card_count']}`",
        f"- Promotion allowed default: `{str(template['promotion_allowed_default']).lower()}`",
        "",
        "## Required Fields",
        "",
    ]
    for field in template["required_model_card_fields"]:
        lines.append(f"- `{field}`")
    lines.extend(
        [
            "",
            "## Artifact Class Rules",
            "",
            "| Artifact class | Method documentation requirement | Not-applicable reason required |",
            "| --- | --- | --- |",
        ]
    )
    for rule in template["artifact_class_rules"]:
        lines.append(
            "| `{artifact_class}` | `{requirement}` | `{reason}` |".format(
                artifact_class=rule["artifact_class"],
                requirement=rule["method_documentation_requirement"],
                reason=str(rule["non_applicability_reason_required"]).lower(),
            )
        )
    lines.extend(
        [
            "",
            "## Forbidden Claims",
            "",
        ]
    )
    for claim in template["forbidden_claims"]:
        lines.append(f"- `{claim}`")
    lines.extend(
        [
            "",
            "## Card Skeleton",
            "",
            "```yaml",
        ]
    )
    for field in template["required_model_card_fields"]:
        default = "false" if field == "promotion_allowed" else "TEMPLATE_REQUIRED"
        lines.append(f"{field}: {default}")
    lines.extend(
        [
            "```",
            "",
            "Interpretive note:",
            "- This file is a template only.",
            "- It does not instantiate model cards.",
            "- It does not authorize simulations, comparisons, validation upgrades, or claim promotion.",
            "",
        ]
    )
    return "\n".join(lines)


def write_template(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    referent_registry_path: Path = DEFAULT_REFERENT_REGISTRY_PATH,
    json_out: Path = DEFAULT_JSON_OUT,
    md_out: Path = DEFAULT_MD_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    template = build_template(
        review_path=review_path,
        referent_registry_path=referent_registry_path,
        captured_at_utc=captured_at_utc,
    )
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(template, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(build_markdown_template(template), encoding="utf-8")
    return template


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the simulation model-card template.")
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW_PATH)
    parser.add_argument("--referent-registry", type=Path, default=DEFAULT_REFERENT_REGISTRY_PATH)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    referent_registry_path = (
        ns.referent_registry if ns.referent_registry.is_absolute() else (REPO_ROOT / ns.referent_registry)
    )
    json_out = ns.json_out if ns.json_out.is_absolute() else (REPO_ROOT / ns.json_out)
    md_out = ns.md_out if ns.md_out.is_absolute() else (REPO_ROOT / ns.md_out)
    template = write_template(
        review_path=review_path,
        referent_registry_path=referent_registry_path,
        json_out=json_out,
        md_out=md_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "simulation_model_card_template_report: "
        f"fields={len(template['required_model_card_fields'])} "
        f"instantiated_model_card_count={template['instantiated_model_card_count']} "
        f"json={_ptr(json_out)} md={_ptr(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
