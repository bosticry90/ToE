from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0"
REGISTRY_ID = "PREDICTION_AND_FALSIFIER_REGISTRY_v0"
PREPARATION_RESULT = (
    "PREDICTION_AND_FALSIFIER_REGISTRY_PREPARED_FROM_MODEL_CARD_TEMPLATE_REVIEW_"
    "WITH_NONCLAIM_TEST_DESIGN_CEILINGS"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_AUDIT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
)
DEFAULT_LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
DEFAULT_NUMERICAL_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
DEFAULT_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_20260515_v0.json"
DEFAULT_PROTOCOL_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json"
)
DEFAULT_REFERENT_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_20260515_v0.json"
DEFAULT_TEMPLATE_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json"
)
DEFAULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_JSON_OUT = (
    REPO_ROOT / "formal" / "docs" / "release" / "PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json"
)
DEFAULT_MD_OUT = REPO_ROOT / "formal" / "docs" / "paper" / "PREDICTION_AND_FALSIFIER_REGISTRY_REPORT_v0.md"

FORBIDDEN_EFFECTS = [
    "prediction_execution",
    "falsifier_execution",
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

ROW_CONFIG_BY_ARTIFACT: dict[str, dict[str, str]] = {
    "C6_CP_NLSE_2D_LANE": {
        "test_design_applicability": "prediction_and_falsifier_relevant",
        "prediction_statement": "candidate_internal_behavior_statement_pending_stronger_registration",
        "falsifier_statement": "artifact_fails_if_norm_dispersion_or_conservation_thresholds_are_violated_under_registered_conditions",
        "observable_or_quantity": "dispersion_or_norm_drift_behavior",
    },
    "C7_MT01A_ACOUSTIC_METRIC_LANE": {
        "test_design_applicability": "prediction_and_falsifier_relevant",
        "prediction_statement": "candidate_acoustic_metric_behavior_statement_pending_stronger_registration",
        "falsifier_statement": "artifact_fails_if_metric_constraint_or_causality_proxy_thresholds_are_violated_under_registered_conditions",
        "observable_or_quantity": "acoustic_metric_constraint_or_causal_proxy_behavior",
    },
    "UCFF_SPECTRAL_AUDIT_LINEAGE": {
        "test_design_applicability": "structural_falsifier_relevant",
        "prediction_statement": "candidate_structural_spectral_behavior_statement_pending_stronger_registration",
        "falsifier_statement": "artifact_fails_if_registered_spectral_or_audit_invariant_checks_break_under_defined_thresholds",
        "observable_or_quantity": "spectral_structure_or_audit_invariant_behavior",
    },
    "BRAGG_DISPERSION_ELIMINATIVE_LANE": {
        "test_design_applicability": "comparator_falsifier_relevant",
        "prediction_statement": "candidate_dispersion_comparator_statement_pending_stronger_registration",
        "falsifier_statement": "artifact_fails_if_dispersion_comparator_residual_or_pruning_threshold_is_violated_under_registered_conditions",
        "observable_or_quantity": "bragg_dispersion_comparator_residual_behavior",
    },
    "RL01_RELATIVISTIC_DISPERSION_LIMIT": {
        "test_design_applicability": "known_limit_falsifier_relevant",
        "prediction_statement": "candidate_relativistic_dispersion_limit_statement_pending_stronger_registration",
        "falsifier_statement": "artifact_fails_if_relativistic_dispersion_scaling_or_causal_proxy_threshold_is_violated_under_registered_conditions",
        "observable_or_quantity": "relativistic_dispersion_limit_behavior",
    },
    "RL02_NONRELATIVISTIC_NLSE_LIMIT": {
        "test_design_applicability": "known_limit_falsifier_relevant",
        "prediction_statement": "candidate_nonrelativistic_nlse_limit_statement_pending_stronger_registration",
        "falsifier_statement": "artifact_fails_if_nlse_limit_scaling_or_residual_threshold_is_violated_under_registered_conditions",
        "observable_or_quantity": "nonrelativistic_nlse_limit_behavior",
    },
    "GR01_DERIVATION_COMPLETENESS_GATE": {
        "test_design_applicability": "governance_falsifier_blocked",
        "prediction_statement": "no_prediction_design_until_derivation_governance_blocker_is_resolved",
        "falsifier_statement": "artifact_remains_blocked_if_required_derivation_or_assumption_discharge_conditions_are_absent",
        "observable_or_quantity": "weak_field_or_poisson_derivation_readiness_condition",
    },
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS": {
        "test_design_applicability": "seam_mismatch_falsifier_relevant",
        "prediction_statement": "candidate_bridge_mismatch_classification_statement_pending_stronger_registration",
        "falsifier_statement": "artifact_fails_if_orthogonality_or_mismatch_witness_thresholds_are_not_reproducible_under_registered_conditions",
        "observable_or_quantity": "bridge_orthogonality_or_mismatch_witness_behavior",
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


def _registry_row(
    referent_row: dict[str, Any],
    *,
    audit_row: dict[str, Any],
    ledger_row: dict[str, Any],
    numerical_row: dict[str, Any],
    matrix_row: dict[str, Any],
    protocol_row: dict[str, Any],
) -> dict[str, Any]:
    artifact_id = str(referent_row["artifact_id"])
    config = ROW_CONFIG_BY_ARTIFACT[artifact_id]
    return {
        "artifact_id": artifact_id,
        "source_audit_id": "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "source_vvuq_ledger_id": "VVUQ_CREDIBILITY_LEDGER_v0",
        "source_numerical_method_registry_id": "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0",
        "source_regime_recovery_matrix_id": "REGIME_RECOVERY_MATRIX_v0",
        "source_sensitivity_robustness_protocol_id": "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0",
        "source_referent_registry_id": "REFERENT_REGISTRY_v0",
        "source_model_card_template_id": "SIMULATION_MODEL_CARD_TEMPLATE_v0",
        "source_artifact_path": audit_row["artifact_path"],
        "test_design_applicability": config["test_design_applicability"],
        "prediction_status": "candidate_not_executed_v0",
        "falsifier_status": "defined_not_executed_v0",
        "prediction_statement": config["prediction_statement"],
        "falsifier_statement": config["falsifier_statement"],
        "observable_or_quantity": config["observable_or_quantity"],
        "pass_fail_criterion_status": "not_fully_registered_v0",
        "execution_status": "not_executed_v0",
        "referent_dependency": referent_row["referent_status"],
        "referent_allowed_use": referent_row["allowed_use"],
        "robustness_dependency": "robustness_protocol_not_executed",
        "source_robustness_status": protocol_row["current_robustness_status"],
        "source_scan_execution_status": protocol_row["scan_execution_status"],
        "method_verification_dependency": referent_row["method_verification_dependency"],
        "source_method_applicability": numerical_row["method_applicability"],
        "source_convergence_status": numerical_row["convergence_status"],
        "source_solver_crosscheck_status": numerical_row["solver_crosscheck_status"],
        "uq_dependency": referent_row["uq_dependency"],
        "source_results_uncertainty": ledger_row["results_uncertainty"],
        "source_recovery_status": matrix_row["matrix_recovery_status"],
        "validation_status": referent_row["validation_status"],
        "validation_status_upgrade_from_source": False,
        "prediction_execution_claim": False,
        "falsifier_execution_claim": False,
        "prediction_result_claim": False,
        "falsifier_result_claim": False,
        "promotion_allowed": False,
        "claim_ceiling": "test_design_registration_only",
        "upgrade_requirements": [
            "define_precise_observable",
            "define_pass_fail_threshold",
            "bind_referent_or_internal_comparator",
            "bind_uncertainty_requirement",
            "bind_robustness_requirement",
            "execute_only_in_later_governed_packet",
        ],
    }


def build_registry(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    numerical_registry_path: Path = DEFAULT_NUMERICAL_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    protocol_path: Path = DEFAULT_PROTOCOL_PATH,
    referent_registry_path: Path = DEFAULT_REFERENT_REGISTRY_PATH,
    template_path: Path = DEFAULT_TEMPLATE_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    audit = _read_json(audit_path)
    ledger = _read_json(ledger_path)
    numerical_registry = _read_json(numerical_registry_path)
    matrix = _read_json(matrix_path)
    protocol = _read_json(protocol_path)
    referent_registry = _read_json(referent_registry_path)
    template = _read_json(template_path)
    review = _read_json(review_path)

    if review.get("accepted") is not True:
        raise ValueError("Cannot prepare prediction/falsifier registry from an unaccepted template result review.")
    if review.get("next_packet") != REGISTRY_ID:
        raise ValueError("Model-card template result review did not authorize prediction/falsifier registry preparation.")
    if review.get("next_packet_authorization_scope") != "PREPARATION_ONLY":
        raise ValueError("Model-card template result review did not restrict prediction/falsifier work to preparation only.")

    audit_by_id = _by_id(audit, "audit_rows")
    ledger_by_id = _by_id(ledger, "ledger_rows")
    numerical_by_id = _by_id(numerical_registry, "registry_rows")
    matrix_by_id = _by_id(matrix, "matrix_rows")
    protocol_by_id = _by_id(protocol, "protocol_rows")
    rows = [
        _registry_row(
            row,
            audit_row=audit_by_id[str(row["artifact_id"])],
            ledger_row=ledger_by_id[str(row["artifact_id"])],
            numerical_row=numerical_by_id[str(row["artifact_id"])],
            matrix_row=matrix_by_id[str(row["artifact_id"])],
            protocol_row=protocol_by_id[str(row["artifact_id"])],
        )
        for row in referent_registry.get("referent_rows", [])
    ]

    prediction_execution_claim_count = sum(1 for row in rows if row["prediction_execution_claim"])
    falsifier_execution_claim_count = sum(1 for row in rows if row["falsifier_execution_claim"])
    prediction_result_claim_count = sum(1 for row in rows if row["prediction_result_claim"])
    falsifier_result_claim_count = sum(1 for row in rows if row["falsifier_result_claim"])
    promotion_allowed_count = sum(1 for row in rows if row["promotion_allowed"])
    validation_upgrade_count = sum(1 for row in rows if row["validation_status_upgrade_from_source"])
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    return {
        "schema_id": SCHEMA_ID,
        "registry_id": REGISTRY_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "preparation_result": PREPARATION_RESULT,
        "consumes_result_review": "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_v0",
        "consumes_result_review_pointer": _ptr(review_path),
        "source_model_card_template": "SIMULATION_MODEL_CARD_TEMPLATE_v0",
        "source_model_card_template_pointer": _ptr(template_path),
        "source_referent_registry": "REFERENT_REGISTRY_v0",
        "source_referent_registry_pointer": _ptr(referent_registry_path),
        "source_sensitivity_robustness_protocol": "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0",
        "source_sensitivity_robustness_protocol_pointer": _ptr(protocol_path),
        "source_regime_recovery_matrix": "REGIME_RECOVERY_MATRIX_v0",
        "source_regime_recovery_matrix_pointer": _ptr(matrix_path),
        "source_numerical_method_registry": "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0",
        "source_numerical_method_registry_pointer": _ptr(numerical_registry_path),
        "source_vvuq_ledger": "VVUQ_CREDIBILITY_LEDGER_v0",
        "source_vvuq_ledger_pointer": _ptr(ledger_path),
        "source_audit": "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "source_audit_pointer": _ptr(audit_path),
        "source_template_scope": template.get("template_scope"),
        "row_count": len(rows),
        "prediction_execution_claim_count": prediction_execution_claim_count,
        "falsifier_execution_claim_count": falsifier_execution_claim_count,
        "prediction_result_claim_count": prediction_result_claim_count,
        "falsifier_result_claim_count": falsifier_result_claim_count,
        "promotion_allowed_count": promotion_allowed_count,
        "all_promotion_allowed_false": promotion_allowed_count == 0,
        "validation_upgrade_count": validation_upgrade_count,
        "primary_falsifier_gap": "PREDICTION_AND_FALSIFIER_PASS_FAIL_CRITERIA_REGISTERED_BUT_NOT_EXECUTED_V0",
        "registry_scope": "REGISTER_TEST_DESIGNS_ONLY_NO_EXECUTION_OR_RESULT_CLAIM",
        "forbidden_effect_status": forbidden_effect_status,
        "scoring_policy": "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "registry_rows": rows,
        "summary": {
            "row_count": len(rows),
            "test_design_applicability_counts": _counts(rows, "test_design_applicability"),
            "prediction_status_counts": _counts(rows, "prediction_status"),
            "falsifier_status_counts": _counts(rows, "falsifier_status"),
            "execution_status_counts": _counts(rows, "execution_status"),
            "pass_fail_criterion_status_counts": _counts(rows, "pass_fail_criterion_status"),
            "method_verification_dependency_counts": _counts(rows, "method_verification_dependency"),
            "uq_dependency_counts": _counts(rows, "uq_dependency"),
            "robustness_dependency_counts": _counts(rows, "robustness_dependency"),
            "next_recommended_action": "REVIEW_PREDICTION_AND_FALSIFIER_REGISTRY_RESULT",
        },
        "non_claim_boundary": (
            "Prediction and falsifier registry only; registers future test designs, observables, pass/fail "
            "requirements, dependencies, and claim ceilings without executing predictions, executing falsifiers, "
            "upgrading validation, discharging theorem debt, moving blockers, reopening lanes, authorizing Phase 2, "
            "claiming empirical validation, closing seams, promoting the master action, or making external-truth claims."
        ),
    }


def build_markdown_report(registry: dict[str, Any]) -> str:
    lines = [
        "# Prediction And Falsifier Registry Report v0",
        "",
        "Spec ID:",
        "- `PREDICTION_AND_FALSIFIER_REGISTRY_REPORT_v0`",
        "",
        "Preparation result:",
        f"- `{registry['preparation_result']}`",
        "",
        "Authority binding:",
        f"- `{registry['authorization_class']}`",
        f"- Consumed result review: `{registry['consumes_result_review_pointer']}`",
        f"- Source model-card template: `{registry['source_model_card_template_pointer']}`",
        f"- Source referent registry: `{registry['source_referent_registry_pointer']}`",
        f"- Source sensitivity/robustness protocol: `{registry['source_sensitivity_robustness_protocol_pointer']}`",
        f"- Source regime-recovery matrix: `{registry['source_regime_recovery_matrix_pointer']}`",
        f"- Source numerical-method registry: `{registry['source_numerical_method_registry_pointer']}`",
        f"- Source VVUQ ledger: `{registry['source_vvuq_ledger_pointer']}`",
        f"- Source audit: `{registry['source_audit_pointer']}`",
        "- JSON registry: `formal/docs/release/PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json`",
        "- Gate: `formal/python/tests/test_prediction_and_falsifier_registry_gate.py`",
        "",
        "Non-claim boundary:",
        f"- {registry['non_claim_boundary']}",
        "",
        "Primary test-design gap:",
        f"- `{registry['primary_falsifier_gap']}`",
        "",
        "Registry scope:",
        f"- `{registry['registry_scope']}`",
        "",
        "## Registry Rows",
        "",
        "| Artifact | Applicability | Prediction status | Falsifier status | Quantity | Criteria | Execution | Method debt | UQ | Promotion |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in registry["registry_rows"]:
        lines.append(
            "| `{artifact}` | `{applicability}` | `{prediction}` | `{falsifier}` | `{quantity}` | `{criteria}` | "
            "`{execution}` | `{method}` | `{uq}` | `{promotion}` |".format(
                artifact=row["artifact_id"],
                applicability=row["test_design_applicability"],
                prediction=row["prediction_status"],
                falsifier=row["falsifier_status"],
                quantity=row["observable_or_quantity"],
                criteria=row["pass_fail_criterion_status"],
                execution=row["execution_status"],
                method=row["method_verification_dependency"],
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
            f"- Prediction execution claim count: `{registry['prediction_execution_claim_count']}`",
            f"- Falsifier execution claim count: `{registry['falsifier_execution_claim_count']}`",
            f"- Next recommended action: `{registry['summary']['next_recommended_action']}`",
            "",
            "Interpretive note:",
            "- This registry records test designs only.",
            "- It does not execute prediction or falsifier checks.",
            "- It does not upgrade validation or authorize physical claim promotion.",
            "",
        ]
    )
    return "\n".join(lines)


def write_registry(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    numerical_registry_path: Path = DEFAULT_NUMERICAL_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    protocol_path: Path = DEFAULT_PROTOCOL_PATH,
    referent_registry_path: Path = DEFAULT_REFERENT_REGISTRY_PATH,
    template_path: Path = DEFAULT_TEMPLATE_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    json_out: Path = DEFAULT_JSON_OUT,
    md_out: Path = DEFAULT_MD_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    registry = build_registry(
        audit_path=audit_path,
        ledger_path=ledger_path,
        numerical_registry_path=numerical_registry_path,
        matrix_path=matrix_path,
        protocol_path=protocol_path,
        referent_registry_path=referent_registry_path,
        template_path=template_path,
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(registry, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(build_markdown_report(registry), encoding="utf-8")
    return registry


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the prediction and falsifier registry.")
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--numerical-registry", type=Path, default=DEFAULT_NUMERICAL_REGISTRY_PATH)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX_PATH)
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL_PATH)
    parser.add_argument("--referent-registry", type=Path, default=DEFAULT_REFERENT_REGISTRY_PATH)
    parser.add_argument("--template", type=Path, default=DEFAULT_TEMPLATE_PATH)
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW_PATH)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    ledger_path = ns.ledger if ns.ledger.is_absolute() else (REPO_ROOT / ns.ledger)
    numerical_registry_path = (
        ns.numerical_registry if ns.numerical_registry.is_absolute() else (REPO_ROOT / ns.numerical_registry)
    )
    matrix_path = ns.matrix if ns.matrix.is_absolute() else (REPO_ROOT / ns.matrix)
    protocol_path = ns.protocol if ns.protocol.is_absolute() else (REPO_ROOT / ns.protocol)
    referent_registry_path = (
        ns.referent_registry if ns.referent_registry.is_absolute() else (REPO_ROOT / ns.referent_registry)
    )
    template_path = ns.template if ns.template.is_absolute() else (REPO_ROOT / ns.template)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    json_out = ns.json_out if ns.json_out.is_absolute() else (REPO_ROOT / ns.json_out)
    md_out = ns.md_out if ns.md_out.is_absolute() else (REPO_ROOT / ns.md_out)
    registry = write_registry(
        audit_path=audit_path,
        ledger_path=ledger_path,
        numerical_registry_path=numerical_registry_path,
        matrix_path=matrix_path,
        protocol_path=protocol_path,
        referent_registry_path=referent_registry_path,
        template_path=template_path,
        review_path=review_path,
        json_out=json_out,
        md_out=md_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "prediction_and_falsifier_registry_report: "
        f"rows={registry['row_count']} "
        f"prediction_execution_claim_count={registry['prediction_execution_claim_count']} "
        f"falsifier_execution_claim_count={registry['falsifier_execution_claim_count']} "
        f"json={_ptr(json_out)} md={_ptr(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
