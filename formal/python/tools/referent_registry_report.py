from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "REFERENT_REGISTRY_20260515_v0"
REGISTRY_ID = "REFERENT_REGISTRY_v0"
PREPARATION_RESULT = (
    "REFERENT_REGISTRY_PREPARED_FROM_SENSITIVITY_ROBUSTNESS_REVIEW_"
    "WITH_NONCLAIM_REFERENT_CEILINGS"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_AUDIT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
)
DEFAULT_LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
DEFAULT_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
DEFAULT_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_20260515_v0.json"
DEFAULT_PROTOCOL_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json"
)
DEFAULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_JSON_OUT = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_20260515_v0.json"
DEFAULT_MD_OUT = REPO_ROOT / "formal" / "docs" / "paper" / "REFERENT_REGISTRY_REPORT_v0.md"

FORBIDDEN_EFFECTS = [
    "theorem_discharge",
    "blocker_movement",
    "lane_reopen",
    "phase2_authorization",
    "empirical_validation_claim",
    "seam_closure",
    "master_action_promotion",
    "external_truth_claim",
]

ROW_CONFIG_BY_ARTIFACT: dict[str, dict[str, str]] = {
    "C6_CP_NLSE_2D_LANE": {
        "referent_applicability": "simulation_internal_or_analytic_referent_relevant",
        "target_quantity": "cp_nlse_like_2d_evolution_behavior",
        "referent_type": "analytic_or_internal_candidate",
        "referent_status": "candidate_not_registered_as_validation",
        "allowed_use": "sanity_check_or_known_limit_context_only",
    },
    "C7_MT01A_ACOUSTIC_METRIC_LANE": {
        "referent_applicability": "simulation_internal_or_analytic_referent_relevant",
        "target_quantity": "acoustic_metric_constraint_behavior",
        "referent_type": "analytic_or_internal_candidate",
        "referent_status": "candidate_not_registered_as_validation",
        "allowed_use": "sanity_check_context_only",
    },
    "UCFF_SPECTRAL_AUDIT_LINEAGE": {
        "referent_applicability": "structural_or_internal_referent_relevant",
        "target_quantity": "ucff_spectral_structure_and_audit_lineage",
        "referent_type": "internal_or_literature_candidate",
        "referent_status": "candidate_not_registered_as_validation",
        "allowed_use": "structural_comparator_context_only",
    },
    "BRAGG_DISPERSION_ELIMINATIVE_LANE": {
        "referent_applicability": "empirical_or_literature_comparator_relevant",
        "target_quantity": "bragg_dispersion_comparator_behavior",
        "referent_type": "empirical_or_literature_candidate",
        "referent_status": "candidate_not_registered_as_validation",
        "allowed_use": "benchmark_pressure_or_falsifier_design_only",
    },
    "RL01_RELATIVISTIC_DISPERSION_LIMIT": {
        "referent_applicability": "known_limit_or_literature_referent_relevant",
        "target_quantity": "relativistic_dispersion_limit_behavior",
        "referent_type": "analytic_or_literature_candidate",
        "referent_status": "candidate_not_registered_as_validation",
        "allowed_use": "known_limit_context_only",
    },
    "RL02_NONRELATIVISTIC_NLSE_LIMIT": {
        "referent_applicability": "known_limit_or_literature_referent_relevant",
        "target_quantity": "nonrelativistic_nlse_limit_behavior",
        "referent_type": "analytic_or_literature_candidate",
        "referent_status": "candidate_not_registered_as_validation",
        "allowed_use": "known_limit_context_only",
    },
    "GR01_DERIVATION_COMPLETENESS_GATE": {
        "referent_applicability": "formal_governance_referent_blocked",
        "target_quantity": "weak_field_or_poisson_governance_requirement",
        "referent_type": "analytic_or_formal_requirement_candidate",
        "referent_status": "blocked_pending_governance_resolution",
        "allowed_use": "blocker_context_only",
    },
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS": {
        "referent_applicability": "seam_or_mismatch_referent_relevant",
        "target_quantity": "bridge_orthogonality_mismatch_classification",
        "referent_type": "internal_report_or_comparator_candidate",
        "referent_status": "candidate_not_registered_as_validation",
        "allowed_use": "mismatch_classification_context_only",
    },
}


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _by_id(payload: dict[str, Any], key: str) -> dict[str, dict[str, Any]]:
    return {str(row["artifact_id"]): row for row in payload.get(key, [])}


def _counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        value = str(row.get(field, "missing"))
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def _referent_row(
    protocol_row: dict[str, Any],
    *,
    audit_row: dict[str, Any],
    ledger_row: dict[str, Any],
    registry_row: dict[str, Any],
    matrix_row: dict[str, Any],
) -> dict[str, Any]:
    artifact_id = str(protocol_row["artifact_id"])
    config = ROW_CONFIG_BY_ARTIFACT[artifact_id]
    validation_status = str(protocol_row["validation_status"])
    return {
        "artifact_id": artifact_id,
        "source_protocol_id": "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0",
        "source_matrix_id": "REGIME_RECOVERY_MATRIX_v0",
        "source_registry_id": "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0",
        "source_ledger_id": "VVUQ_CREDIBILITY_LEDGER_v0",
        "source_audit_id": "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "source_artifact_path": audit_row["artifact_path"],
        "referent_applicability": config["referent_applicability"],
        "target_quantity": config["target_quantity"],
        "referent_type": config["referent_type"],
        "referent_status": config["referent_status"],
        "allowed_use": config["allowed_use"],
        "comparison_execution_status": "not_executed_v0",
        "referent_uncertainty_status": "not_registered_v0",
        "source_recovery_status": matrix_row["matrix_recovery_status"],
        "source_robustness_status": protocol_row["current_robustness_status"],
        "method_verification_dependency": protocol_row["method_verification_dependency"],
        "source_method_applicability": registry_row["method_applicability"],
        "source_convergence_status": registry_row["convergence_status"],
        "source_solver_crosscheck_status": registry_row["solver_crosscheck_status"],
        "uq_dependency": protocol_row["uq_dependency"],
        "source_results_uncertainty": ledger_row["results_uncertainty"],
        "validation_status": validation_status,
        "source_validation_status": validation_status,
        "validation_status_upgrade_from_source": False,
        "empirical_validation_claim": False,
        "referent_comparison_execution_claim": False,
        "promotion_allowed": False,
        "claim_ceiling": "referent_registration_only",
        "upgrade_requirements": [
            "register_specific_referent_identity",
            "record_source_type_and_provenance",
            "define_allowed_comparison_use",
            "record_uncertainty_or_tolerance_status",
            "define_comparison_quantity",
            "execute_comparison_only_in_later_governed_packet",
        ],
    }


def build_registry(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    protocol_path: Path = DEFAULT_PROTOCOL_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    audit = _read_json(audit_path)
    ledger = _read_json(ledger_path)
    registry = _read_json(registry_path)
    matrix = _read_json(matrix_path)
    protocol = _read_json(protocol_path)
    review = _read_json(review_path)

    if review.get("accepted") is not True:
        raise ValueError("Cannot prepare referent registry from an unaccepted robustness result review.")
    if review.get("next_packet") != REGISTRY_ID:
        raise ValueError("Robustness result review did not authorize referent registry preparation.")
    if review.get("next_packet_authorization_scope") != "PREPARATION_ONLY":
        raise ValueError("Robustness result review did not restrict referent registry work to preparation only.")

    audit_by_id = _by_id(audit, "audit_rows")
    ledger_by_id = _by_id(ledger, "ledger_rows")
    registry_by_id = _by_id(registry, "registry_rows")
    matrix_by_id = _by_id(matrix, "matrix_rows")
    rows = [
        _referent_row(
            row,
            audit_row=audit_by_id[str(row["artifact_id"])],
            ledger_row=ledger_by_id[str(row["artifact_id"])],
            registry_row=registry_by_id[str(row["artifact_id"])],
            matrix_row=matrix_by_id[str(row["artifact_id"])],
        )
        for row in protocol.get("protocol_rows", [])
    ]

    promotion_allowed_count = sum(1 for row in rows if row["promotion_allowed"])
    validation_upgrade_count = sum(1 for row in rows if row["validation_status_upgrade_from_source"])
    referent_comparison_execution_claim_count = sum(1 for row in rows if row["referent_comparison_execution_claim"])
    empirical_validation_claim_count = sum(1 for row in rows if row["empirical_validation_claim"])
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    return {
        "schema_id": SCHEMA_ID,
        "registry_id": REGISTRY_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "preparation_result": PREPARATION_RESULT,
        "consumes_result_review": "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_v0",
        "consumes_result_review_pointer": _ptr(review_path),
        "source_protocol": "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0",
        "source_protocol_pointer": _ptr(protocol_path),
        "source_matrix": "REGIME_RECOVERY_MATRIX_v0",
        "source_matrix_pointer": _ptr(matrix_path),
        "source_registry": "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0",
        "source_registry_pointer": _ptr(registry_path),
        "source_vvuq_ledger": "VVUQ_CREDIBILITY_LEDGER_v0",
        "source_vvuq_ledger_pointer": _ptr(ledger_path),
        "source_audit": "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "source_audit_pointer": _ptr(audit_path),
        "row_count": len(rows),
        "promotion_allowed_count": promotion_allowed_count,
        "all_promotion_allowed_false": promotion_allowed_count == 0,
        "validation_upgrade_count": validation_upgrade_count,
        "referent_comparison_execution_claim_count": referent_comparison_execution_claim_count,
        "empirical_validation_claim_count": empirical_validation_claim_count,
        "primary_referent_gap": "REFERENT_IDENTIFICATION_ALLOWED_USE_AND_UNCERTAINTY_REGISTRATION_INCOMPLETE_V0",
        "registry_scope": "REGISTER_REFERENTS_ONLY_NO_COMPARISON_OR_VALIDATION_EXECUTION_CLAIM",
        "forbidden_effect_status": forbidden_effect_status,
        "scoring_policy": "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "referent_rows": rows,
        "summary": {
            "row_count": len(rows),
            "referent_applicability_counts": _counts(rows, "referent_applicability"),
            "referent_type_counts": _counts(rows, "referent_type"),
            "allowed_use_counts": _counts(rows, "allowed_use"),
            "comparison_execution_status_counts": _counts(rows, "comparison_execution_status"),
            "referent_uncertainty_status_counts": _counts(rows, "referent_uncertainty_status"),
            "uq_dependency_counts": _counts(rows, "uq_dependency"),
            "next_recommended_action": "REVIEW_REFERENT_REGISTRY_RESULT",
        },
        "non_claim_boundary": (
            "Referent registry only; registers candidate referent categories, allowed uses, uncertainty gaps, "
            "and comparison quantities without executing comparisons, upgrading validation, discharging theorem "
            "debt, moving blockers, reopening lanes, authorizing Phase 2, claiming empirical validation, closing "
            "seams, promoting the master action, or making external-truth claims."
        ),
    }


def build_markdown_report(registry: dict[str, Any]) -> str:
    lines = [
        "# Referent Registry Report v0",
        "",
        "Spec ID:",
        "- `REFERENT_REGISTRY_REPORT_v0`",
        "",
        "Preparation result:",
        f"- `{registry['preparation_result']}`",
        "",
        "Authority binding:",
        f"- `{registry['authorization_class']}`",
        f"- Consumed result review: `{registry['consumes_result_review_pointer']}`",
        f"- Source protocol: `{registry['source_protocol_pointer']}`",
        f"- Source matrix: `{registry['source_matrix_pointer']}`",
        f"- Source registry: `{registry['source_registry_pointer']}`",
        f"- Source VVUQ ledger: `{registry['source_vvuq_ledger_pointer']}`",
        f"- Source audit: `{registry['source_audit_pointer']}`",
        "- JSON registry: `formal/docs/release/REFERENT_REGISTRY_20260515_v0.json`",
        "- Gate: `formal/python/tests/test_referent_registry_gate.py`",
        "",
        "Non-claim boundary:",
        f"- {registry['non_claim_boundary']}",
        "",
        "Primary referent gap:",
        f"- `{registry['primary_referent_gap']}`",
        "",
        "Registry scope:",
        f"- `{registry['registry_scope']}`",
        "",
        "## Referent Rows",
        "",
        "| Artifact | Applicability | Target quantity | Referent type | Allowed use | Comparison | Uncertainty | UQ | Promotion |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in registry["referent_rows"]:
        lines.append(
            "| `{artifact}` | `{applicability}` | `{target}` | `{rtype}` | `{allowed}` | `{comparison}` | "
            "`{uncertainty}` | `{uq}` | `{promotion}` |".format(
                artifact=row["artifact_id"],
                applicability=row["referent_applicability"],
                target=row["target_quantity"],
                rtype=row["referent_type"],
                allowed=row["allowed_use"],
                comparison=row["comparison_execution_status"],
                uncertainty=row["referent_uncertainty_status"],
                uq=row["uq_dependency"],
                promotion=str(row["promotion_allowed"]).lower(),
            )
        )
    lines.extend(
        [
            "",
            "## Summary",
            "",
            f"- Row count: `{registry['summary']['row_count']}`",
            f"- Promotion allowed count: `{registry['promotion_allowed_count']}`",
            f"- Validation upgrade count: `{registry['validation_upgrade_count']}`",
            f"- Referent comparison execution claim count: `{registry['referent_comparison_execution_claim_count']}`",
            f"- Empirical validation claim count: `{registry['empirical_validation_claim_count']}`",
            f"- Next recommended action: `{registry['summary']['next_recommended_action']}`",
            "",
            "Interpretive note:",
            "- This registry records candidate referent categories and allowed uses only.",
            "- It does not execute comparisons.",
            "- It does not upgrade validation or authorize physical claim promotion.",
            "",
        ]
    )
    return "\n".join(lines)


def write_registry(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    protocol_path: Path = DEFAULT_PROTOCOL_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    json_out: Path = DEFAULT_JSON_OUT,
    md_out: Path = DEFAULT_MD_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    registry = build_registry(
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        matrix_path=matrix_path,
        protocol_path=protocol_path,
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(registry, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(build_markdown_report(registry), encoding="utf-8")
    return registry


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the referent registry.")
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY_PATH)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX_PATH)
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL_PATH)
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW_PATH)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    ledger_path = ns.ledger if ns.ledger.is_absolute() else (REPO_ROOT / ns.ledger)
    registry_path = ns.registry if ns.registry.is_absolute() else (REPO_ROOT / ns.registry)
    matrix_path = ns.matrix if ns.matrix.is_absolute() else (REPO_ROOT / ns.matrix)
    protocol_path = ns.protocol if ns.protocol.is_absolute() else (REPO_ROOT / ns.protocol)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    json_out = ns.json_out if ns.json_out.is_absolute() else (REPO_ROOT / ns.json_out)
    md_out = ns.md_out if ns.md_out.is_absolute() else (REPO_ROOT / ns.md_out)
    registry = write_registry(
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        matrix_path=matrix_path,
        protocol_path=protocol_path,
        review_path=review_path,
        json_out=json_out,
        md_out=md_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "referent_registry_report: "
        f"rows={registry['row_count']} "
        f"promotion_allowed_count={registry['promotion_allowed_count']} "
        f"json={_ptr(json_out)} md={_ptr(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
