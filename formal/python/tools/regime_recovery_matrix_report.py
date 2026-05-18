from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "REGIME_RECOVERY_MATRIX_20260515_v0"
MATRIX_ID = "REGIME_RECOVERY_MATRIX_v0"
PREPARATION_RESULT = (
    "REGIME_RECOVERY_MATRIX_PREPARED_FROM_NUMERICAL_METHOD_REGISTRY_REVIEW_"
    "WITH_NONCLAIM_KNOWN_LIMIT_CEILINGS"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_AUDIT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
)
DEFAULT_LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
DEFAULT_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
DEFAULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_JSON_OUT = REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_20260515_v0.json"
DEFAULT_MD_OUT = REPO_ROOT / "formal" / "docs" / "paper" / "REGIME_RECOVERY_MATRIX_REPORT_v0.md"

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

ROW_CONFIG_BY_ARTIFACT: dict[str, dict[str, Any]] = {
    "C6_CP_NLSE_2D_LANE": {
        "regime_recovery_applicability": "known_limit_recovery_relevant",
        "target_regime": "nonlinear_nlse_like_internal_limit",
        "known_limit_or_comparator": "CP_NLSE_like_dispersion_and_norm_drift_internal_limit",
        "matrix_recovery_status": "partial",
        "pass_fail_criterion_status": "partial",
        "referent_status": "analytic_referent_candidate",
        "method_verification_dependency": "method_debt_visible_convergence_mms_or_solver_crosscheck_unresolved_v0",
        "claim_ceiling": "internal_consequence_only",
        "upgrade_requirements": [
            "register_explicit_known_limit_target",
            "define_pass_fail_criterion",
            "register_analytic_or_literature_referent",
            "connect_numerical_method_verification_dependency",
            "record_uncertainty_or_sensitivity_requirement",
            "execute_bounded_recovery_test_or_record_blocker",
        ],
    },
    "C7_MT01A_ACOUSTIC_METRIC_LANE": {
        "regime_recovery_applicability": "known_limit_recovery_relevant",
        "target_regime": "acoustic_geometry_emergent_metric_limit",
        "known_limit_or_comparator": "acoustic_metric_or_effective_geometry_candidate_limit",
        "matrix_recovery_status": "candidate",
        "pass_fail_criterion_status": "partial",
        "referent_status": "analytic_referent_candidate",
        "method_verification_dependency": "method_debt_visible_convergence_mms_or_solver_crosscheck_unresolved_v0",
        "claim_ceiling": "validation_candidate_only",
        "upgrade_requirements": [
            "register_explicit_known_limit_target",
            "define_pass_fail_criterion",
            "register_analytic_or_literature_referent",
            "connect_numerical_method_verification_dependency",
            "record_uncertainty_or_sensitivity_requirement",
            "execute_bounded_recovery_test_or_record_blocker",
        ],
    },
    "UCFF_SPECTRAL_AUDIT_LINEAGE": {
        "regime_recovery_applicability": "regime_comparator_relevant",
        "target_regime": "structural_spectral_regime_relevance",
        "known_limit_or_comparator": "UCFF_symbolic_and_spectral_front_door_invariant_pressure",
        "matrix_recovery_status": "candidate",
        "pass_fail_criterion_status": "not_registered_v0",
        "referent_status": "not_registered_v0",
        "method_verification_dependency": "method_verification_not_applicable_report_surface",
        "claim_ceiling": "internal_consequence_only",
        "upgrade_requirements": [
            "register_explicit_regime_target_or_mark_comparator_only",
            "define_pass_fail_criterion",
            "register_referent_if_regime_recovery_is_claimed_later",
            "preserve_report_surface_method_nonapplicability",
            "record_uncertainty_or_sensitivity_requirement",
        ],
    },
    "BRAGG_DISPERSION_ELIMINATIVE_LANE": {
        "regime_recovery_applicability": "regime_comparator_relevant",
        "target_regime": "bragg_dispersion_comparator_regime",
        "known_limit_or_comparator": "BEC_Bragg_dispersion_empirical_comparator_candidate",
        "matrix_recovery_status": "candidate",
        "pass_fail_criterion_status": "partial",
        "referent_status": "empirical_referent_candidate",
        "method_verification_dependency": "method_verification_not_applicable_comparator_surface",
        "claim_ceiling": "validation_candidate_only",
        "upgrade_requirements": [
            "register_comparator_pass_fail_criterion",
            "register_referent_domain_and_uncertainty",
            "keep_comparator_relevance_separate_from_recovery_status",
            "record_uncertainty_or_sensitivity_requirement",
        ],
    },
    "RL01_RELATIVISTIC_DISPERSION_LIMIT": {
        "regime_recovery_applicability": "known_limit_recovery_relevant",
        "target_regime": "relativistic_dispersion_limit",
        "known_limit_or_comparator": "Lorentz_compatible_relativistic_dispersion_comparator",
        "matrix_recovery_status": "partial",
        "pass_fail_criterion_status": "partial",
        "referent_status": "literature_referent_candidate",
        "method_verification_dependency": "method_verification_not_applicable_comparator_surface",
        "claim_ceiling": "known_limit_relevance_only",
        "upgrade_requirements": [
            "register_explicit_known_limit_target",
            "define_pass_fail_criterion",
            "register_analytic_or_literature_referent",
            "record_uncertainty_or_sensitivity_requirement",
            "execute_bounded_recovery_test_or_record_blocker",
        ],
    },
    "RL02_NONRELATIVISTIC_NLSE_LIMIT": {
        "regime_recovery_applicability": "known_limit_recovery_relevant",
        "target_regime": "nonrelativistic_nlse_limit",
        "known_limit_or_comparator": "Schrodinger_or_NLSE_like_nonrelativistic_limit",
        "matrix_recovery_status": "partial",
        "pass_fail_criterion_status": "partial",
        "referent_status": "literature_referent_candidate",
        "method_verification_dependency": "method_verification_not_applicable_comparator_surface",
        "claim_ceiling": "known_limit_relevance_only",
        "upgrade_requirements": [
            "register_explicit_known_limit_target",
            "define_pass_fail_criterion",
            "register_analytic_or_literature_referent",
            "record_uncertainty_or_sensitivity_requirement",
            "execute_bounded_recovery_test_or_record_blocker",
        ],
    },
    "GR01_DERIVATION_COMPLETENESS_GATE": {
        "regime_recovery_applicability": "formal_governance_blocked",
        "target_regime": "weak_field_poisson_gravity_limit",
        "known_limit_or_comparator": "weak_field_Poisson_or_Newtonian_gravity_recovery_governance_surface",
        "matrix_recovery_status": "blocked",
        "pass_fail_criterion_status": "blocked",
        "referent_status": "blocked",
        "method_verification_dependency": "method_verification_not_applicable_formal_governance_surface",
        "claim_ceiling": "blocked_no_upgrade",
        "upgrade_requirements": [
            "resolve_derivation_governance_blocker",
            "register_explicit_known_limit_target",
            "define_pass_fail_criterion_after_blocker_resolution",
            "register_analytic_or_literature_referent_after_blocker_resolution",
        ],
    },
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS": {
        "regime_recovery_applicability": "seam_or_mismatch_relevant",
        "target_regime": "cross_pillar_seam_mismatch_evidence",
        "known_limit_or_comparator": "bridge_orthogonality_and_mismatch_report_surface",
        "matrix_recovery_status": "not_applicable",
        "pass_fail_criterion_status": "not_applicable",
        "referent_status": "not_applicable",
        "method_verification_dependency": "method_verification_not_applicable_report_surface",
        "claim_ceiling": "nonclaim_bookkeeping_only",
        "upgrade_requirements": [
            "keep_as_seam_mismatch_or_failure_evidence",
            "do_not_treat_orthogonality_report_as_known_limit_recovery",
            "register_recovery_target_only_if_a_separate_limit_surface_is_created",
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


def _matrix_row(
    registry_row: dict[str, Any],
    *,
    audit_row: dict[str, Any],
    ledger_row: dict[str, Any],
    source_registry_id: str,
) -> dict[str, Any]:
    artifact_id = str(registry_row["artifact_id"])
    config = ROW_CONFIG_BY_ARTIFACT[artifact_id]
    validation_status = str(registry_row["validation_status"])
    return {
        "artifact_id": artifact_id,
        "source_registry_id": source_registry_id,
        "source_audit_id": "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "source_ledger_id": registry_row["source_ledger_id"],
        "source_artifact_path": audit_row["artifact_path"],
        "regime_recovery_applicability": config["regime_recovery_applicability"],
        "target_regime": config["target_regime"],
        "known_limit_or_comparator": config["known_limit_or_comparator"],
        "source_known_limit_status": audit_row["known_limit_status"],
        "matrix_recovery_status": config["matrix_recovery_status"],
        "pass_fail_criterion_status": config["pass_fail_criterion_status"],
        "referent_status": config["referent_status"],
        "method_verification_dependency": config["method_verification_dependency"],
        "source_method_applicability": registry_row["method_applicability"],
        "source_convergence_status": registry_row["convergence_status"],
        "source_manufactured_solution_status": registry_row["manufactured_solution_status"],
        "source_solver_crosscheck_status": registry_row["solver_crosscheck_status"],
        "uq_dependency": UQ_DEPENDENCY_BY_LEDGER_UNCERTAINTY[str(ledger_row["results_uncertainty"])],
        "validation_status": validation_status,
        "source_validation_status": validation_status,
        "validation_status_upgrade_from_source": False,
        "recovery_completion_claim": False,
        "promotion_allowed": False,
        "claim_ceiling": config["claim_ceiling"],
        "upgrade_requirements": config["upgrade_requirements"],
    }


def build_matrix(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    audit = _read_json(audit_path)
    ledger = _read_json(ledger_path)
    registry = _read_json(registry_path)
    review = _read_json(review_path)

    if review.get("accepted") is not True:
        raise ValueError("Cannot prepare regime-recovery matrix from an unaccepted numerical-method result review.")
    if review.get("next_packet") != MATRIX_ID:
        raise ValueError("Numerical-method result review did not authorize regime-recovery matrix preparation.")
    if review.get("next_packet_authorization_scope") != "PREPARATION_ONLY":
        raise ValueError("Numerical-method result review did not restrict matrix work to preparation only.")

    audit_by_id = _by_id(audit, "audit_rows")
    ledger_by_id = _by_id(ledger, "ledger_rows")
    registry_rows = list(registry.get("registry_rows", []))
    rows = [
        _matrix_row(
            row,
            audit_row=audit_by_id[str(row["artifact_id"])],
            ledger_row=ledger_by_id[str(row["artifact_id"])],
            source_registry_id=str(registry["registry_id"]),
        )
        for row in registry_rows
    ]
    promotion_allowed_count = sum(1 for row in rows if row["promotion_allowed"])
    validation_upgrade_count = sum(1 for row in rows if row["validation_status_upgrade_from_source"])
    recovery_completion_claim_count = sum(1 for row in rows if row["recovery_completion_claim"])
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    return {
        "schema_id": SCHEMA_ID,
        "matrix_id": MATRIX_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "preparation_result": PREPARATION_RESULT,
        "consumes_result_review": "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_v0",
        "consumes_result_review_pointer": _ptr(review_path),
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
        "recovery_completion_claim_count": recovery_completion_claim_count,
        "primary_regime_gap": "KNOWN_LIMIT_PASS_FAIL_CRITERIA_AND_RECOVERY_EVIDENCE_DEPTH_NOT_COMPLETE_V0",
        "forbidden_effect_status": forbidden_effect_status,
        "scoring_policy": "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "matrix_rows": rows,
        "summary": {
            "row_count": len(rows),
            "regime_recovery_applicability_counts": _counts(rows, "regime_recovery_applicability"),
            "matrix_recovery_status_counts": _counts(rows, "matrix_recovery_status"),
            "pass_fail_criterion_status_counts": _counts(rows, "pass_fail_criterion_status"),
            "referent_status_counts": _counts(rows, "referent_status"),
            "next_recommended_action": "REVIEW_REGIME_RECOVERY_MATRIX_RESULT",
        },
        "non_claim_boundary": (
            "Regime-recovery matrix only; records known-limit and regime-recovery posture without theorem "
            "discharge, blocker movement, lane reopen, Phase 2 authorization, empirical validation claim, "
            "seam closure, master-action promotion, recovery completion claim, or external-truth claim."
        ),
    }


def build_markdown_report(matrix: dict[str, Any]) -> str:
    lines = [
        "# Regime Recovery Matrix Report v0",
        "",
        "Spec ID:",
        "- `REGIME_RECOVERY_MATRIX_REPORT_v0`",
        "",
        "Preparation result:",
        f"- `{matrix['preparation_result']}`",
        "",
        "Authority binding:",
        f"- `{matrix['authorization_class']}`",
        f"- Consumed result review: `{matrix['consumes_result_review_pointer']}`",
        f"- Source registry: `{matrix['source_registry_pointer']}`",
        f"- Source VVUQ ledger: `{matrix['source_vvuq_ledger_pointer']}`",
        f"- Source audit: `{matrix['source_audit_pointer']}`",
        "- JSON matrix: `formal/docs/release/REGIME_RECOVERY_MATRIX_20260515_v0.json`",
        "- Gate: `formal/python/tests/test_regime_recovery_matrix_gate.py`",
        "",
        "Non-claim boundary:",
        f"- {matrix['non_claim_boundary']}",
        "",
        "Primary regime gap:",
        f"- `{matrix['primary_regime_gap']}`",
        "",
        "## Matrix Rows",
        "",
        "| Artifact | Applicability | Target regime | Source status | Matrix status | Criterion | Referent | Method dependency | Promotion |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in matrix["matrix_rows"]:
        lines.append(
            "| `{artifact}` | `{applicability}` | `{target}` | `{source}` | `{status}` | `{criterion}` | "
            "`{referent}` | `{method}` | `{promotion}` |".format(
                artifact=row["artifact_id"],
                applicability=row["regime_recovery_applicability"],
                target=row["target_regime"],
                source=row["source_known_limit_status"],
                status=row["matrix_recovery_status"],
                criterion=row["pass_fail_criterion_status"],
                referent=row["referent_status"],
                method=row["method_verification_dependency"],
                promotion=str(row["promotion_allowed"]).lower(),
            )
        )
    lines.extend(
        [
            "",
            "## Summary",
            "",
            f"- Row count: `{matrix['summary']['row_count']}`",
            f"- Promotion allowed count: `{matrix['promotion_allowed_count']}`",
            f"- Validation upgrade count: `{matrix['validation_upgrade_count']}`",
            f"- Recovery completion claim count: `{matrix['recovery_completion_claim_count']}`",
            f"- Next recommended action: `{matrix['summary']['next_recommended_action']}`",
            "",
            "Interpretive note:",
            "- This matrix records known-limit and regime-recovery posture over the existing lineage.",
            "- It does not run new simulations, finish pass/fail criteria, register referents, or upgrade validation.",
            "",
        ]
    )
    return "\n".join(lines)


def write_matrix(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    json_out: Path = DEFAULT_JSON_OUT,
    md_out: Path = DEFAULT_MD_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    matrix = build_matrix(
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(matrix, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(build_markdown_report(matrix), encoding="utf-8")
    return matrix


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the regime-recovery matrix.")
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY_PATH)
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
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    json_out = ns.json_out if ns.json_out.is_absolute() else (REPO_ROOT / ns.json_out)
    md_out = ns.md_out if ns.md_out.is_absolute() else (REPO_ROOT / ns.md_out)
    matrix = write_matrix(
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        review_path=review_path,
        json_out=json_out,
        md_out=md_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "regime_recovery_matrix_report: "
        f"rows={matrix['row_count']} "
        f"promotion_allowed_count={matrix['promotion_allowed_count']} "
        f"json={_ptr(json_out)} md={_ptr(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
