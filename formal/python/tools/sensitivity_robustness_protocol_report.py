from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0"
PROTOCOL_ID = "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0"
PREPARATION_RESULT = (
    "SENSITIVITY_ROBUSTNESS_PROTOCOL_PREPARED_FROM_REGIME_RECOVERY_REVIEW_"
    "WITH_NONCLAIM_ROBUSTNESS_CEILINGS"
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
DEFAULT_REVIEW_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_JSON_OUT = (
    REPO_ROOT / "formal" / "docs" / "release" / "SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json"
)
DEFAULT_MD_OUT = REPO_ROOT / "formal" / "docs" / "paper" / "SENSITIVITY_ROBUSTNESS_PROTOCOL_REPORT_v0.md"

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

SIMULATION_SCANS = [
    "parameter_perturbation",
    "initial_condition_perturbation",
    "boundary_condition_perturbation",
    "resolution_perturbation",
    "solver_tolerance_perturbation",
    "noise_or_seed_perturbation_where_applicable",
]

COMPARATOR_SCANS = [
    "input_data_or_reference_perturbation",
    "threshold_sensitivity",
    "referent_uncertainty_sensitivity",
    "comparator_window_or_domain_perturbation",
    "provenance_lock_consistency_check",
]

GOVERNANCE_SCANS = [
    "assumption_ledger_delta_check",
    "blocker_status_review",
    "formal_dependency_perturbation_review",
]

SEAM_REPORT_SCANS = [
    "mismatch_threshold_sensitivity",
    "orthogonality_witness_perturbation",
    "report_determinism_rerun",
    "failure_classification_delta_check",
]

ROW_CONFIG_BY_ARTIFACT: dict[str, dict[str, Any]] = {
    "C6_CP_NLSE_2D_LANE": {
        "robustness_applicability": "simulation_or_numerical_method_surface",
        "required_scans": SIMULATION_SCANS,
        "method_verification_dependency": "method_debt_visible",
        "upgrade_requirements": [
            "define_scan_parameters",
            "define_pass_fail_thresholds",
            "register_resolution_and_solver_tolerance_grid",
            "execute_bounded_scan_or_record_blocker",
            "record_failure_envelope",
            "record_sensitivity_ranking",
        ],
    },
    "C7_MT01A_ACOUSTIC_METRIC_LANE": {
        "robustness_applicability": "simulation_or_numerical_method_surface",
        "required_scans": SIMULATION_SCANS,
        "method_verification_dependency": "method_debt_visible",
        "upgrade_requirements": [
            "define_scan_parameters",
            "define_pass_fail_thresholds",
            "register_resolution_and_solver_tolerance_grid",
            "execute_bounded_scan_or_record_blocker",
            "record_failure_envelope",
            "record_sensitivity_ranking",
        ],
    },
    "UCFF_SPECTRAL_AUDIT_LINEAGE": {
        "robustness_applicability": "comparator_or_report_surface",
        "required_scans": COMPARATOR_SCANS,
        "method_verification_dependency": "method_verification_not_applicable_report_surface",
        "upgrade_requirements": [
            "define_symbolic_invariant_perturbation_scope",
            "define_threshold_sensitivity_rule",
            "record_report_or_comparator_failure_envelope",
            "record_sensitivity_ranking",
        ],
    },
    "BRAGG_DISPERSION_ELIMINATIVE_LANE": {
        "robustness_applicability": "comparator_or_report_surface",
        "required_scans": COMPARATOR_SCANS,
        "method_verification_dependency": "method_verification_not_applicable_comparator_surface",
        "upgrade_requirements": [
            "define_digitization_or_reference_perturbation_scope",
            "define_comparator_pass_fail_thresholds",
            "record_referent_uncertainty_sensitivity",
            "record_failure_envelope",
        ],
    },
    "RL01_RELATIVISTIC_DISPERSION_LIMIT": {
        "robustness_applicability": "comparator_or_report_surface",
        "required_scans": COMPARATOR_SCANS,
        "method_verification_dependency": "method_verification_not_applicable_comparator_surface",
        "upgrade_requirements": [
            "define_known_limit_threshold_sensitivity",
            "record_reference_or_domain_perturbation_scope",
            "record_uncertainty_or_tolerance_requirement",
            "record_failure_envelope",
        ],
    },
    "RL02_NONRELATIVISTIC_NLSE_LIMIT": {
        "robustness_applicability": "comparator_or_report_surface",
        "required_scans": COMPARATOR_SCANS,
        "method_verification_dependency": "method_verification_not_applicable_comparator_surface",
        "upgrade_requirements": [
            "define_known_limit_threshold_sensitivity",
            "record_reference_or_domain_perturbation_scope",
            "record_uncertainty_or_tolerance_requirement",
            "record_failure_envelope",
        ],
    },
    "GR01_DERIVATION_COMPLETENESS_GATE": {
        "robustness_applicability": "formal_governance_surface",
        "required_scans": GOVERNANCE_SCANS,
        "method_verification_dependency": "method_verification_not_applicable_formal_governance_surface",
        "upgrade_requirements": [
            "resolve_governance_blocker_before_scan_execution",
            "define_assumption_delta_review_scope",
            "record_blocker_failure_envelope",
            "preserve_no_upgrade_status",
        ],
    },
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS": {
        "robustness_applicability": "seam_or_mismatch_report_surface",
        "required_scans": SEAM_REPORT_SCANS,
        "method_verification_dependency": "method_verification_not_applicable_report_surface",
        "upgrade_requirements": [
            "define_mismatch_threshold_sensitivity",
            "define_orthogonality_witness_perturbation_scope",
            "record_failure_classification_envelope",
            "preserve_report_determinism_gate",
        ],
    },
}

UQ_DEPENDENCY_BY_LEDGER_UNCERTAINTY = {
    "not_quantified": "uq_not_quantified",
    "qualitative": "uq_qualitative",
    "partial_quantitative": "uq_partial_quantitative",
    "quantitative": "uq_quantitative",
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


def _protocol_row(
    matrix_row: dict[str, Any],
    *,
    audit_row: dict[str, Any],
    ledger_row: dict[str, Any],
    registry_row: dict[str, Any],
) -> dict[str, Any]:
    artifact_id = str(matrix_row["artifact_id"])
    config = ROW_CONFIG_BY_ARTIFACT[artifact_id]
    validation_status = str(matrix_row["validation_status"])
    return {
        "artifact_id": artifact_id,
        "source_matrix_id": "REGIME_RECOVERY_MATRIX_v0",
        "source_registry_id": matrix_row["source_registry_id"],
        "source_ledger_id": matrix_row["source_ledger_id"],
        "source_audit_id": "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "source_artifact_path": audit_row["artifact_path"],
        "robustness_applicability": config["robustness_applicability"],
        "required_scans": config["required_scans"],
        "current_robustness_status": ledger_row["results_robustness"],
        "scan_execution_status": "not_executed_v0",
        "failure_envelope_status": "not_registered_v0",
        "sensitivity_ranking_status": "not_registered_v0",
        "confidence_label_status": "not_registered_v0",
        "method_verification_dependency": config["method_verification_dependency"],
        "source_method_applicability": registry_row["method_applicability"],
        "source_convergence_status": registry_row["convergence_status"],
        "source_solver_crosscheck_status": registry_row["solver_crosscheck_status"],
        "uq_dependency": UQ_DEPENDENCY_BY_LEDGER_UNCERTAINTY[str(ledger_row["results_uncertainty"])],
        "source_recovery_status": matrix_row["matrix_recovery_status"],
        "validation_status": validation_status,
        "source_validation_status": validation_status,
        "validation_status_upgrade_from_source": False,
        "robustness_completion_claim": False,
        "promotion_allowed": False,
        "claim_ceiling": "robustness_protocol_bookkeeping_only",
        "upgrade_requirements": config["upgrade_requirements"],
    }


def build_protocol(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    audit = _read_json(audit_path)
    ledger = _read_json(ledger_path)
    registry = _read_json(registry_path)
    matrix = _read_json(matrix_path)
    review = _read_json(review_path)

    if review.get("accepted") is not True:
        raise ValueError("Cannot prepare sensitivity/robustness protocol from an unaccepted regime-matrix result review.")
    if review.get("next_packet") != PROTOCOL_ID:
        raise ValueError("Regime-matrix result review did not authorize sensitivity/robustness protocol preparation.")
    if review.get("next_packet_authorization_scope") != "PREPARATION_ONLY":
        raise ValueError("Regime-matrix result review did not restrict protocol work to preparation only.")

    audit_by_id = _by_id(audit, "audit_rows")
    ledger_by_id = _by_id(ledger, "ledger_rows")
    registry_by_id = _by_id(registry, "registry_rows")
    rows = [
        _protocol_row(
            row,
            audit_row=audit_by_id[str(row["artifact_id"])],
            ledger_row=ledger_by_id[str(row["artifact_id"])],
            registry_row=registry_by_id[str(row["artifact_id"])],
        )
        for row in matrix.get("matrix_rows", [])
    ]
    promotion_allowed_count = sum(1 for row in rows if row["promotion_allowed"])
    validation_upgrade_count = sum(1 for row in rows if row["validation_status_upgrade_from_source"])
    robustness_completion_claim_count = sum(1 for row in rows if row["robustness_completion_claim"])
    scan_execution_claim_count = sum(1 for row in rows if row["scan_execution_status"] != "not_executed_v0")
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    return {
        "schema_id": SCHEMA_ID,
        "protocol_id": PROTOCOL_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "preparation_result": PREPARATION_RESULT,
        "consumes_result_review": "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_v0",
        "consumes_result_review_pointer": _ptr(review_path),
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
        "robustness_completion_claim_count": robustness_completion_claim_count,
        "scan_execution_claim_count": scan_execution_claim_count,
        "validation_upgrade_count": validation_upgrade_count,
        "primary_robustness_gap": "PERTURBATION_RESOLUTION_SOLVER_TOLERANCE_AND_FAILURE_ENVELOPE_PROTOCOL_NOT_EXECUTED_V0",
        "protocol_scope": "DEFINE_ROBUSTNESS_REQUIREMENTS_ONLY_NO_SCAN_EXECUTION_CLAIM",
        "forbidden_effect_status": forbidden_effect_status,
        "scoring_policy": "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "protocol_rows": rows,
        "summary": {
            "row_count": len(rows),
            "robustness_applicability_counts": _counts(rows, "robustness_applicability"),
            "current_robustness_status_counts": _counts(rows, "current_robustness_status"),
            "scan_execution_status_counts": _counts(rows, "scan_execution_status"),
            "uq_dependency_counts": _counts(rows, "uq_dependency"),
            "next_recommended_action": "REVIEW_SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT",
        },
        "non_claim_boundary": (
            "Sensitivity/robustness protocol only; defines required scans and robustness bookkeeping without "
            "executing scans, claiming robustness completion, upgrading validation, discharging theorem debt, "
            "moving blockers, reopening lanes, authorizing Phase 2, claiming empirical validation, closing seams, "
            "promoting the master action, or making external-truth claims."
        ),
    }


def build_markdown_report(protocol: dict[str, Any]) -> str:
    lines = [
        "# Sensitivity Robustness Protocol Report v0",
        "",
        "Spec ID:",
        "- `SENSITIVITY_ROBUSTNESS_PROTOCOL_REPORT_v0`",
        "",
        "Preparation result:",
        f"- `{protocol['preparation_result']}`",
        "",
        "Authority binding:",
        f"- `{protocol['authorization_class']}`",
        f"- Consumed result review: `{protocol['consumes_result_review_pointer']}`",
        f"- Source matrix: `{protocol['source_matrix_pointer']}`",
        f"- Source registry: `{protocol['source_registry_pointer']}`",
        f"- Source VVUQ ledger: `{protocol['source_vvuq_ledger_pointer']}`",
        f"- Source audit: `{protocol['source_audit_pointer']}`",
        "- JSON protocol: `formal/docs/release/SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json`",
        "- Gate: `formal/python/tests/test_sensitivity_robustness_protocol_gate.py`",
        "",
        "Non-claim boundary:",
        f"- {protocol['non_claim_boundary']}",
        "",
        "Primary robustness gap:",
        f"- `{protocol['primary_robustness_gap']}`",
        "",
        "Protocol scope:",
        f"- `{protocol['protocol_scope']}`",
        "",
        "## Protocol Rows",
        "",
        "| Artifact | Applicability | Robustness | Scan execution | Failure envelope | Sensitivity ranking | UQ | Method dependency | Promotion |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in protocol["protocol_rows"]:
        lines.append(
            "| `{artifact}` | `{applicability}` | `{robustness}` | `{scan}` | `{failure}` | `{sensitivity}` | "
            "`{uq}` | `{method}` | `{promotion}` |".format(
                artifact=row["artifact_id"],
                applicability=row["robustness_applicability"],
                robustness=row["current_robustness_status"],
                scan=row["scan_execution_status"],
                failure=row["failure_envelope_status"],
                sensitivity=row["sensitivity_ranking_status"],
                uq=row["uq_dependency"],
                method=row["method_verification_dependency"],
                promotion=str(row["promotion_allowed"]).lower(),
            )
        )
    lines.extend(
        [
            "",
            "## Summary",
            "",
            f"- Row count: `{protocol['summary']['row_count']}`",
            f"- Promotion allowed count: `{protocol['promotion_allowed_count']}`",
            f"- Robustness completion claim count: `{protocol['robustness_completion_claim_count']}`",
            f"- Scan execution claim count: `{protocol['scan_execution_claim_count']}`",
            f"- Next recommended action: `{protocol['summary']['next_recommended_action']}`",
            "",
            "Interpretive note:",
            "- This protocol defines robustness obligations over the existing lineage.",
            "- It does not execute perturbation, resolution, solver-tolerance, noise, or comparator scans.",
            "- It does not claim robustness completion or upgrade validation.",
            "",
        ]
    )
    return "\n".join(lines)


def write_protocol(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    json_out: Path = DEFAULT_JSON_OUT,
    md_out: Path = DEFAULT_MD_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    protocol = build_protocol(
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        matrix_path=matrix_path,
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(protocol, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(build_markdown_report(protocol), encoding="utf-8")
    return protocol


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the sensitivity/robustness protocol.")
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY_PATH)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX_PATH)
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
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    json_out = ns.json_out if ns.json_out.is_absolute() else (REPO_ROOT / ns.json_out)
    md_out = ns.md_out if ns.md_out.is_absolute() else (REPO_ROOT / ns.md_out)
    protocol = write_protocol(
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        matrix_path=matrix_path,
        review_path=review_path,
        json_out=json_out,
        md_out=md_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "sensitivity_robustness_protocol_report: "
        f"rows={protocol['row_count']} "
        f"promotion_allowed_count={protocol['promotion_allowed_count']} "
        f"json={_ptr(json_out)} md={_ptr(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
