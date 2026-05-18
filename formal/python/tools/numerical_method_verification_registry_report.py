from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0"
REGISTRY_ID = "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0"
PREPARATION_RESULT = (
    "NUMERICAL_METHOD_VERIFICATION_REGISTRY_PREPARED_FROM_VVUQ_REVIEW_"
    "WITH_NONCLAIM_METHOD_VERIFICATION_CEILINGS"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
DEFAULT_AUDIT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
)
DEFAULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_JSON_OUT = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
DEFAULT_MD_OUT = REPO_ROOT / "formal" / "docs" / "paper" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_REPORT_v0.md"

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

METHOD_REGISTRY_BY_ARTIFACT: dict[str, dict[str, Any]] = {
    "C6_CP_NLSE_2D_LANE": {
        "method_applicability": "numerical_method_applicable",
        "equation_or_system_solved": "CP-NLSE-like 2D evolution system",
        "discretization_family": "recorded_or_pending",
        "time_integrator": "recorded_or_pending",
        "spatial_operator": "recorded_or_pending",
        "formal_order_claimed": "not_registered_v0",
        "observed_order_status": "not_measured",
        "convergence_status": "not_registered_v0",
        "exact_solution_benchmark_status": "present_partial",
        "manufactured_solution_status": "not_registered_v0",
        "conservation_diagnostic_status": "present_partial",
        "stability_condition_status": "not_registered_v0",
        "solver_crosscheck_status": "not_performed",
        "failure_modes_registered": True,
        "verification_depth": "gated_but_not_convergence_verified",
        "non_numerical_method_reason": "",
        "method_verification_readout": "gated_evolution_lane_but_convergence_mms_and_solver_crosschecks_not_registered",
        "upgrade_requirements": [
            "register_discretization",
            "register_time_integrator_and_spatial_operator",
            "register_formal_order_or_mark_not_applicable",
            "run_resolution_convergence_scan",
            "add_exact_or_manufactured_solution_benchmark_where_applicable",
            "record stability and conservation diagnostics",
            "perform_solver_crosscheck_or_record_blocker",
        ],
    },
    "C7_MT01A_ACOUSTIC_METRIC_LANE": {
        "method_applicability": "numerical_method_applicable",
        "equation_or_system_solved": "acoustic-metric diagnostic and inequality system",
        "discretization_family": "recorded_or_pending",
        "time_integrator": "not_registered_v0",
        "spatial_operator": "recorded_or_pending",
        "formal_order_claimed": "not_registered_v0",
        "observed_order_status": "not_measured",
        "convergence_status": "not_registered_v0",
        "exact_solution_benchmark_status": "not_registered_v0",
        "manufactured_solution_status": "candidate",
        "conservation_diagnostic_status": "not_registered_v0",
        "stability_condition_status": "present_partial",
        "solver_crosscheck_status": "not_performed",
        "failure_modes_registered": True,
        "verification_depth": "gated_but_not_convergence_verified",
        "non_numerical_method_reason": "",
        "method_verification_readout": "diagnostic_lane_has_perturbation_pressure_but_method_order_and_convergence_are_unregistered",
        "upgrade_requirements": [
            "register_discretization",
            "register_operator_scope_for_metric_diagnostics",
            "register_formal_order_or_mark_not_applicable",
            "run_resolution_convergence_scan",
            "decide_exact_or_manufactured_solution_benchmark_scope",
            "record stability condition and solver tolerance assumptions",
            "perform_solver_crosscheck_or_record_blocker",
        ],
    },
    "UCFF_SPECTRAL_AUDIT_LINEAGE": {
        "method_applicability": "comparator_or_report_surface",
        "equation_or_system_solved": "not_applicable",
        "discretization_family": "not_applicable",
        "time_integrator": "not_applicable",
        "spatial_operator": "not_applicable",
        "formal_order_claimed": "not_applicable",
        "observed_order_status": "not_applicable",
        "convergence_status": "not_applicable",
        "exact_solution_benchmark_status": "not_applicable",
        "manufactured_solution_status": "not_applicable",
        "conservation_diagnostic_status": "not_applicable",
        "stability_condition_status": "not_applicable",
        "solver_crosscheck_status": "not_applicable",
        "failure_modes_registered": True,
        "verification_depth": "not_applicable",
        "non_numerical_method_reason": "front-door and symbolic-invariant audit surface without a registered discretized evolution method",
        "method_verification_readout": "verification_relevant_report_surface_not_a_numerical_method_registry_target_in_v0",
        "upgrade_requirements": [
            "keep_as_report_or_comparator_surface",
            "register_a_numerical_method_only_if_a_solver_surface_is_separately_authorized",
        ],
    },
    "BRAGG_DISPERSION_ELIMINATIVE_LANE": {
        "method_applicability": "comparator_or_report_surface",
        "equation_or_system_solved": "not_applicable",
        "discretization_family": "not_applicable",
        "time_integrator": "not_applicable",
        "spatial_operator": "not_applicable",
        "formal_order_claimed": "not_applicable",
        "observed_order_status": "not_applicable",
        "convergence_status": "not_applicable",
        "exact_solution_benchmark_status": "not_applicable",
        "manufactured_solution_status": "not_applicable",
        "conservation_diagnostic_status": "not_applicable",
        "stability_condition_status": "not_applicable",
        "solver_crosscheck_status": "not_applicable",
        "failure_modes_registered": True,
        "verification_depth": "not_applicable",
        "non_numerical_method_reason": "empirical-comparator and eliminative dispersion lane rather than a registered solver/discretization method",
        "method_verification_readout": "comparator_quality_and_uncertainty_are_relevant_but_numerical_method_order_is_not_applicable_in_v0",
        "upgrade_requirements": [
            "keep_comparator_uncertainty_and_digitization_provenance_separate_from_method_verification",
            "register_solver_method_only_if_a_forward_simulation_lane_is_added",
        ],
    },
    "RL01_RELATIVISTIC_DISPERSION_LIMIT": {
        "method_applicability": "comparator_or_report_surface",
        "equation_or_system_solved": "not_applicable",
        "discretization_family": "not_applicable",
        "time_integrator": "not_applicable",
        "spatial_operator": "not_applicable",
        "formal_order_claimed": "not_applicable",
        "observed_order_status": "not_applicable",
        "convergence_status": "not_applicable",
        "exact_solution_benchmark_status": "not_applicable",
        "manufactured_solution_status": "not_applicable",
        "conservation_diagnostic_status": "not_applicable",
        "stability_condition_status": "not_applicable",
        "solver_crosscheck_status": "not_applicable",
        "failure_modes_registered": True,
        "verification_depth": "not_applicable",
        "non_numerical_method_reason": "known-limit comparator/front-door surface without a registered numerical evolution method",
        "method_verification_readout": "known_limit_comparator_is_validation_relevant_but_not_a_numerical_method_verification_row",
        "upgrade_requirements": [
            "keep_known_limit_comparison_criteria_explicit",
            "register_numerical_method_fields_only_if_a_solver_or_discretization_is_added",
        ],
    },
    "RL02_NONRELATIVISTIC_NLSE_LIMIT": {
        "method_applicability": "comparator_or_report_surface",
        "equation_or_system_solved": "not_applicable",
        "discretization_family": "not_applicable",
        "time_integrator": "not_applicable",
        "spatial_operator": "not_applicable",
        "formal_order_claimed": "not_applicable",
        "observed_order_status": "not_applicable",
        "convergence_status": "not_applicable",
        "exact_solution_benchmark_status": "not_applicable",
        "manufactured_solution_status": "not_applicable",
        "conservation_diagnostic_status": "not_applicable",
        "stability_condition_status": "not_applicable",
        "solver_crosscheck_status": "not_applicable",
        "failure_modes_registered": True,
        "verification_depth": "not_applicable",
        "non_numerical_method_reason": "known-limit comparator/front-door surface without a registered numerical evolution method",
        "method_verification_readout": "known_limit_comparator_is_validation_relevant_but_not_a_numerical_method_verification_row",
        "upgrade_requirements": [
            "keep_known_limit_comparison_criteria_explicit",
            "register_numerical_method_fields_only_if_a_solver_or_discretization_is_added",
        ],
    },
    "GR01_DERIVATION_COMPLETENESS_GATE": {
        "method_applicability": "formal_or_governance_surface",
        "equation_or_system_solved": "not_applicable",
        "discretization_family": "not_applicable",
        "time_integrator": "not_applicable",
        "spatial_operator": "not_applicable",
        "formal_order_claimed": "not_applicable",
        "observed_order_status": "not_applicable",
        "convergence_status": "not_applicable",
        "exact_solution_benchmark_status": "not_applicable",
        "manufactured_solution_status": "not_applicable",
        "conservation_diagnostic_status": "not_applicable",
        "stability_condition_status": "not_applicable",
        "solver_crosscheck_status": "not_applicable",
        "failure_modes_registered": True,
        "verification_depth": "not_applicable",
        "non_numerical_method_reason": "derivation-completeness governance gate, not a numerical solver or discretization surface",
        "method_verification_readout": "method_verification_not_applicable_until_a_numerical_method_surface_is_created",
        "upgrade_requirements": [
            "resolve_derivation_governance_blocker_before_method_verification_can_upgrade_any_related_claim",
            "do_not_force_solver_fields_onto_a_formal_governance_gate",
        ],
    },
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS": {
        "method_applicability": "comparator_or_report_surface",
        "equation_or_system_solved": "not_applicable",
        "discretization_family": "not_applicable",
        "time_integrator": "not_applicable",
        "spatial_operator": "not_applicable",
        "formal_order_claimed": "not_applicable",
        "observed_order_status": "not_applicable",
        "convergence_status": "not_applicable",
        "exact_solution_benchmark_status": "not_applicable",
        "manufactured_solution_status": "not_applicable",
        "conservation_diagnostic_status": "not_applicable",
        "stability_condition_status": "not_applicable",
        "solver_crosscheck_status": "not_applicable",
        "failure_modes_registered": True,
        "verification_depth": "not_applicable",
        "non_numerical_method_reason": "orthogonality report generator and seam-stress evidence surface, not a numerical method-bearing model",
        "method_verification_readout": "report_surface_can_preserve_failure_evidence_but_has_no_method_order_to_verify_in_v0",
        "upgrade_requirements": [
            "keep_orthogonality_report_reproducibility_gated",
            "register_numerical_method_fields_only_if_a_solver_surface_is_added",
        ],
    },
}


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


def _audit_by_id(audit: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(row["artifact_id"]): row for row in audit.get("audit_rows", [])}


def _registry_row(
    ledger_row: dict[str, Any],
    *,
    audit_row: dict[str, Any],
    source_ledger_id: str,
) -> dict[str, Any]:
    artifact_id = str(ledger_row["artifact_id"])
    method = METHOD_REGISTRY_BY_ARTIFACT[artifact_id]
    validation_status = str(ledger_row["validation_status"])
    return {
        "artifact_id": artifact_id,
        "source_ledger_id": source_ledger_id,
        "source_audit_id": ledger_row["source_audit_id"],
        "source_artifact_path": audit_row["artifact_path"],
        "method_applicability": method["method_applicability"],
        "equation_or_system_solved": method["equation_or_system_solved"],
        "discretization_family": method["discretization_family"],
        "time_integrator": method["time_integrator"],
        "spatial_operator": method["spatial_operator"],
        "formal_order_claimed": method["formal_order_claimed"],
        "observed_order_status": method["observed_order_status"],
        "convergence_status": method["convergence_status"],
        "exact_solution_benchmark_status": method["exact_solution_benchmark_status"],
        "manufactured_solution_status": method["manufactured_solution_status"],
        "conservation_diagnostic_status": method["conservation_diagnostic_status"],
        "stability_condition_status": method["stability_condition_status"],
        "solver_crosscheck_status": method["solver_crosscheck_status"],
        "failure_modes_registered": method["failure_modes_registered"],
        "verification_depth": method["verification_depth"],
        "non_numerical_method_reason": method["non_numerical_method_reason"],
        "validation_status": validation_status,
        "source_validation_status": validation_status,
        "validation_status_upgrade_from_ledger": False,
        "claim_status": ledger_row["claim_status"],
        "source_claim_ceiling": ledger_row["claim_ceiling"],
        "claim_ceiling": "method_verification_bookkeeping_only",
        "method_verification_readout": method["method_verification_readout"],
        "upgrade_requirements": method["upgrade_requirements"],
        "promotion_allowed": False,
    }


def _validation_upgrade_count(rows: list[dict[str, Any]]) -> int:
    return sum(1 for row in rows if row["validation_status_upgrade_from_ledger"])


def build_registry(
    *,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    ledger = _read_json(ledger_path)
    audit = _read_json(audit_path)
    review = _read_json(review_path)

    if review.get("accepted") is not True:
        raise ValueError("Cannot prepare numerical-method registry from an unaccepted VVUQ result review.")
    if review.get("next_packet") != REGISTRY_ID:
        raise ValueError("VVUQ result review did not authorize numerical-method registry preparation.")
    if review.get("next_packet_authorization_scope") != "PREPARATION_ONLY":
        raise ValueError("VVUQ result review did not restrict registry work to preparation only.")

    audit_rows_by_id = _audit_by_id(audit)
    rows = [
        _registry_row(
            row,
            audit_row=audit_rows_by_id[str(row["artifact_id"])],
            source_ledger_id=str(ledger["ledger_id"]),
        )
        for row in ledger.get("ledger_rows", [])
    ]
    promotion_allowed_count = sum(1 for row in rows if row["promotion_allowed"])
    numerical_rows = [row for row in rows if row["method_applicability"] == "numerical_method_applicable"]
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    return {
        "schema_id": SCHEMA_ID,
        "registry_id": REGISTRY_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "preparation_result": PREPARATION_RESULT,
        "consumes_result_review": "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_v0",
        "consumes_result_review_pointer": _ptr(review_path),
        "source_ledger": "VVUQ_CREDIBILITY_LEDGER_v0",
        "source_ledger_pointer": _ptr(ledger_path),
        "source_audit": "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "source_audit_pointer": _ptr(audit_path),
        "source_audit_row_count": len(audit.get("audit_rows", [])),
        "row_count": len(rows),
        "promotion_allowed_count": promotion_allowed_count,
        "all_promotion_allowed_false": promotion_allowed_count == 0,
        "validation_upgrade_count": _validation_upgrade_count(rows),
        "scoring_policy": "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "method_verification_scope": "REGISTER_VERIFICATION_DEPTH_ONLY_NO_COMPLETION_CLAIM",
        "primary_method_gap": "CONVERGENCE_MMS_EXACT_SOLUTION_AND_SOLVER_CROSSCHECK_DEPTH_NOT_REGISTERED_V0",
        "forbidden_effect_status": forbidden_effect_status,
        "registry_rows": rows,
        "summary": {
            "row_count": len(rows),
            "method_applicability_counts": _counts(rows, "method_applicability"),
            "verification_depth_counts": _counts(rows, "verification_depth"),
            "numerical_method_applicable_count": len(numerical_rows),
            "convergence_not_registered_count": sum(
                1 for row in numerical_rows if row["convergence_status"] == "not_registered_v0"
            ),
            "manufactured_solution_not_passed_count": sum(
                1 for row in numerical_rows if row["manufactured_solution_status"] not in {"passed"}
            ),
            "solver_crosscheck_not_performed_count": sum(
                1 for row in numerical_rows if row["solver_crosscheck_status"] == "not_performed"
            ),
            "next_recommended_action": "REVIEW_NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT",
        },
        "non_claim_boundary": (
            "Numerical-method verification registry only; it registers method-verification depth and debt "
            "without theorem discharge, blocker movement, lane reopen, Phase 2 authorization, empirical "
            "validation claim, seam closure, master-action promotion, or external-truth claim."
        ),
    }


def build_markdown_report(registry: dict[str, Any]) -> str:
    lines = [
        "# Numerical Method Verification Registry Report v0",
        "",
        "Spec ID:",
        "- `NUMERICAL_METHOD_VERIFICATION_REGISTRY_REPORT_v0`",
        "",
        "Preparation result:",
        f"- `{registry['preparation_result']}`",
        "",
        "Authority binding:",
        f"- `{registry['authorization_class']}`",
        f"- Consumed result review: `{registry['consumes_result_review_pointer']}`",
        f"- Source ledger: `{registry['source_ledger_pointer']}`",
        f"- Source audit: `{registry['source_audit_pointer']}`",
        "- JSON registry: `formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json`",
        "- Gate: `formal/python/tests/test_numerical_method_verification_registry_gate.py`",
        "",
        "Non-claim boundary:",
        f"- {registry['non_claim_boundary']}",
        "",
        "Method-verification scope:",
        f"- `{registry['method_verification_scope']}`",
        "",
        "Primary method gap:",
        f"- `{registry['primary_method_gap']}`",
        "",
        "Scoring policy:",
        f"- `{registry['scoring_policy']}`",
        "",
        "## Registry Rows",
        "",
        "| Artifact | Applicability | Equation/System | Convergence | Exact benchmark | MMS | Solver crosscheck | Depth | Promotion |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in registry["registry_rows"]:
        lines.append(
            "| `{artifact}` | `{applicability}` | `{system}` | `{convergence}` | `{exact}` | "
            "`{mms}` | `{solver}` | `{depth}` | `{promotion}` |".format(
                artifact=row["artifact_id"],
                applicability=row["method_applicability"],
                system=row["equation_or_system_solved"],
                convergence=row["convergence_status"],
                exact=row["exact_solution_benchmark_status"],
                mms=row["manufactured_solution_status"],
                solver=row["solver_crosscheck_status"],
                depth=row["verification_depth"],
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
            f"- Numerical-method applicable rows: `{registry['summary']['numerical_method_applicable_count']}`",
            f"- Next recommended action: `{registry['summary']['next_recommended_action']}`",
            "",
            "Interpretive note:",
            "- This registry records method-verification debt over the already audited surfaces.",
            "- It does not complete convergence, MMS, exact-solution, stability, or solver-crosscheck verification.",
            "- It does not validate the ToE or upgrade any source validation status.",
            "",
        ]
    )
    return "\n".join(lines)


def write_registry(
    *,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    json_out: Path = DEFAULT_JSON_OUT,
    md_out: Path = DEFAULT_MD_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    registry = build_registry(
        ledger_path=ledger_path,
        audit_path=audit_path,
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(registry, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(build_markdown_report(registry), encoding="utf-8")
    return registry


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the numerical-method verification registry.")
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW_PATH)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    ledger_path = ns.ledger if ns.ledger.is_absolute() else (REPO_ROOT / ns.ledger)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    json_out = ns.json_out if ns.json_out.is_absolute() else (REPO_ROOT / ns.json_out)
    md_out = ns.md_out if ns.md_out.is_absolute() else (REPO_ROOT / ns.md_out)
    registry = write_registry(
        ledger_path=ledger_path,
        audit_path=audit_path,
        review_path=review_path,
        json_out=json_out,
        md_out=md_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "numerical_method_verification_registry_report: "
        f"rows={registry['row_count']} "
        f"promotion_allowed_count={registry['promotion_allowed_count']} "
        f"json={_ptr(json_out)} md={_ptr(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
