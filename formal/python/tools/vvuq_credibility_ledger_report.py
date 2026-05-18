from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "VVUQ_CREDIBILITY_LEDGER_20260515_v0"
LEDGER_ID = "VVUQ_CREDIBILITY_LEDGER_v0"
PREPARATION_RESULT = "VVUQ_CREDIBILITY_LEDGER_PREPARED_FROM_CAPABILITY_AUDIT_WITH_NONCLAIM_CREDIBILITY_CEILINGS"
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_AUDIT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
)
DEFAULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_JSON_OUT = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
DEFAULT_MD_OUT = REPO_ROOT / "formal" / "docs" / "paper" / "VVUQ_CREDIBILITY_LEDGER_REPORT_v0.md"


CLAIM_CEILING_BY_BOUNDARY = {
    "nonclaim": "nonclaim_computational_support_only",
    "internal_consequence": "internal_consequence_only",
    "known_limit_relevant": "known_limit_relevance_only",
    "validation_candidate": "validation_candidate_only",
    "blocked": "blocked_no_upgrade",
}

UNCERTAINTY_BY_AUDIT_UQ = {
    "none": "not_quantified",
    "qualitative": "qualitative",
    "partial": "partial_quantitative",
    "quantitative": "quantitative",
}

INPUT_PEDIGREE_BY_ARTIFACT = {
    "C6_CP_NLSE_2D_LANE": "repo_internal",
    "C7_MT01A_ACOUSTIC_METRIC_LANE": "repo_internal",
    "UCFF_SPECTRAL_AUDIT_LINEAGE": "repo_internal",
    "BRAGG_DISPERSION_ELIMINATIVE_LANE": "mixed",
    "RL01_RELATIVISTIC_DISPERSION_LIMIT": "mixed",
    "RL02_NONRELATIVISTIC_NLSE_LIMIT": "mixed",
    "GR01_DERIVATION_COMPLETENESS_GATE": "supplied_assumption",
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS": "repo_internal",
}

USE_HISTORY_BY_ARTIFACT = {
    "C6_CP_NLSE_2D_LANE": "existing_gated_lane",
    "C7_MT01A_ACOUSTIC_METRIC_LANE": "existing_gated_lane",
    "UCFF_SPECTRAL_AUDIT_LINEAGE": "existing_gated_front_door",
    "BRAGG_DISPERSION_ELIMINATIVE_LANE": "existing_gated_comparator",
    "RL01_RELATIVISTIC_DISPERSION_LIMIT": "existing_gated_comparator",
    "RL02_NONRELATIVISTIC_NLSE_LIMIT": "existing_gated_comparator",
    "GR01_DERIVATION_COMPLETENESS_GATE": "existing_gated_derivation_governance",
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS": "existing_gated_bridge_report",
}


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _model_family(row: dict[str, Any]) -> str:
    domains = [str(value) for value in row.get("physics_domain", [])]
    if "cross_pillar" in domains:
        return "cross_pillar"
    if "nonlinear_field" in domains:
        return "nonlinear_field"
    if domains:
        return domains[0]
    return "general"


def _credibility_readout(*, row: dict[str, Any], results_uncertainty: str) -> str:
    validation = str(row["validation_status"])
    robustness = str(row["robustness_status"])
    known_limit = str(row["known_limit_status"])
    if row["claim_boundary"] == "blocked":
        return "blocked_or_governance_limited_no_credibility_upgrade"
    if results_uncertainty == "not_quantified" and validation in {"none", "internal_only"}:
        return "verification_present_but_uq_and_validation_depth_limited"
    if results_uncertainty == "not_quantified":
        return "verification_present_but_uq_missing"
    if validation in {"known_limit_candidate", "empirical_candidate"}:
        return "verification_present_validation_candidate_but_not_validated"
    if robustness in {"partial", "perturbation_scanned"} and known_limit in {"candidate", "partial"}:
        return "bounded_robustness_and_known_limit_pressure_without_promotion"
    return "bounded_nonclaim_credibility_bookkeeping_only"


def _upgrade_requirements(row: dict[str, Any], results_uncertainty: str) -> list[str]:
    requirements: list[str] = []
    if results_uncertainty in {"not_quantified", "qualitative"}:
        requirements.append("quantitative_uncertainty_estimate")
    if row["robustness_status"] == "partial":
        requirements.append("resolution_or_solver_sensitivity_scan")
    if row["robustness_status"] == "perturbation_scanned":
        requirements.append("broaden_to_resolution_or_solver_crosscheck")
    if row["validation_status"] in {"none", "internal_only"}:
        requirements.append("known_limit_or_referent_comparison_where_applicable")
    if row["validation_status"] in {"known_limit_candidate", "empirical_candidate"}:
        requirements.append("executed_validation_comparison_with_uncertainty_and_domain")
    if row["known_limit_status"] in {"candidate", "partial"}:
        requirements.append("explicit_pass_fail_known_limit_criterion")
    if row["falsifier_status"] == "defined":
        requirements.append("execute_defined_falsifier_or_record_blocker")
    if row["falsifier_status"] == "blocked":
        requirements.append("resolve_falsifier_blocker_before_credibility_upgrade")
    return requirements or ["maintain_nonclaim_boundary_and_repeatability"]


def _ledger_row(row: dict[str, Any], *, source_audit_id: str) -> dict[str, Any]:
    artifact_id = str(row["artifact_id"])
    claim_boundary = str(row["claim_boundary"])
    results_uncertainty = UNCERTAINTY_BY_AUDIT_UQ[str(row["uq_status"])]
    return {
        "artifact_id": artifact_id,
        "source_audit_id": source_audit_id,
        "model_family": _model_family(row),
        "verification_status": row["verification_status"],
        "validation_status": row["validation_status"],
        "input_pedigree": INPUT_PEDIGREE_BY_ARTIFACT[artifact_id],
        "results_uncertainty": results_uncertainty,
        "results_robustness": row["robustness_status"],
        "use_history": USE_HISTORY_BY_ARTIFACT[artifact_id],
        "management_status": "roadmap_pinned_gated",
        "claim_status": claim_boundary,
        "claim_ceiling": CLAIM_CEILING_BY_BOUNDARY[claim_boundary],
        "credibility_readout": _credibility_readout(row=row, results_uncertainty=results_uncertainty),
        "upgrade_requirements": _upgrade_requirements(row, results_uncertainty),
        "source_audit_reference": row["artifact_path"],
        "promotion_allowed": False,
    }


def build_ledger(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    audit = _read_json(audit_path)
    review = _read_json(review_path)

    if review.get("accepted") is not True:
        raise ValueError("Cannot prepare VVUQ ledger from an unaccepted capability-audit result review.")
    if review.get("next_packet") != LEDGER_ID:
        raise ValueError("Capability-audit result review did not authorize VVUQ ledger preparation.")

    rows = [_ledger_row(row, source_audit_id=str(audit["audit_id"])) for row in audit.get("audit_rows", [])]
    promotion_allowed_count = sum(1 for row in rows if row["promotion_allowed"])
    return {
        "schema_id": SCHEMA_ID,
        "ledger_id": LEDGER_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "preparation_result": PREPARATION_RESULT,
        "consumes_result_review": "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_v0",
        "consumes_result_review_pointer": _ptr(review_path),
        "source_audit": "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "source_audit_pointer": _ptr(audit_path),
        "source_audit_row_count": len(audit.get("audit_rows", [])),
        "primary_gap_pattern": "UQ_DEPTH_AND_VALIDATION_DEPTH_ARE_PRIMARY_NEXT_CREDIBILITY_GAPS",
        "promotion_allowed_count": promotion_allowed_count,
        "all_promotion_allowed_false": promotion_allowed_count == 0,
        "scoring_policy": "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "ledger_rows": rows,
        "summary": {
            "row_count": len(rows),
            "results_uncertainty_counts": _counts(rows, "results_uncertainty"),
            "validation_status_counts": _counts(rows, "validation_status"),
            "claim_ceiling_counts": _counts(rows, "claim_ceiling"),
            "next_recommended_action": "REVIEW_VVUQ_CREDIBILITY_LEDGER_RESULT",
        },
        "non_claim_boundary": (
            "Credibility bookkeeping only; no theorem discharge, blocker movement, lane reopen, "
            "Phase 2 authorization, empirical validation claim, seam closure, master-action promotion, "
            "or external-truth claim."
        ),
    }


def _counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        value = str(row.get(field, "missing"))
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def build_markdown_report(ledger: dict[str, Any]) -> str:
    lines = [
        "# VVUQ Credibility Ledger Report v0",
        "",
        "Spec ID:",
        "- `VVUQ_CREDIBILITY_LEDGER_REPORT_v0`",
        "",
        "Preparation result:",
        f"- `{ledger['preparation_result']}`",
        "",
        "Authority binding:",
        f"- `{ledger['authorization_class']}`",
        f"- Source audit: `{ledger['source_audit_pointer']}`",
        f"- Consumed result review: `{ledger['consumes_result_review_pointer']}`",
        "- JSON ledger: `formal/docs/release/VVUQ_CREDIBILITY_LEDGER_20260515_v0.json`",
        "- Gate: `formal/python/tests/test_vvuq_credibility_ledger_gate.py`",
        "",
        "Non-claim boundary:",
        f"- {ledger['non_claim_boundary']}",
        "",
        "Primary gap pattern:",
        f"- `{ledger['primary_gap_pattern']}`",
        "",
        "Scoring policy:",
        f"- `{ledger['scoring_policy']}`",
        "",
        "## Ledger Rows",
        "",
        "| Artifact | Verification | Validation | Input pedigree | Uncertainty | Robustness | Claim ceiling | Readout | Promotion |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in ledger["ledger_rows"]:
        lines.append(
            "| `{artifact_id}` | `{verification}` | `{validation}` | `{pedigree}` | `{uncertainty}` | "
            "`{robustness}` | `{ceiling}` | `{readout}` | `{promotion}` |".format(
                artifact_id=row["artifact_id"],
                verification=row["verification_status"],
                validation=row["validation_status"],
                pedigree=row["input_pedigree"],
                uncertainty=row["results_uncertainty"],
                robustness=row["results_robustness"],
                ceiling=row["claim_ceiling"],
                readout=row["credibility_readout"],
                promotion=str(row["promotion_allowed"]).lower(),
            )
        )
    lines.extend(
        [
            "",
            "## Summary",
            "",
            f"- Row count: `{ledger['summary']['row_count']}`",
            f"- Promotion allowed count: `{ledger['promotion_allowed_count']}`",
            f"- Next recommended action: `{ledger['summary']['next_recommended_action']}`",
            "",
            "Interpretive note:",
            "- This ledger records credibility bookkeeping over the audited computational surfaces.",
            "- It does not alter the source audit classification and does not validate the ToE.",
            "",
        ]
    )
    return "\n".join(lines)


def write_ledger(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    review_path: Path = DEFAULT_REVIEW_PATH,
    json_out: Path = DEFAULT_JSON_OUT,
    md_out: Path = DEFAULT_MD_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    ledger = build_ledger(audit_path=audit_path, review_path=review_path, captured_at_utc=captured_at_utc)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(build_markdown_report(ledger), encoding="utf-8")
    return ledger


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the VVUQ credibility ledger.")
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW_PATH)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    json_out = ns.json_out if ns.json_out.is_absolute() else (REPO_ROOT / ns.json_out)
    md_out = ns.md_out if ns.md_out.is_absolute() else (REPO_ROOT / ns.md_out)
    ledger = write_ledger(
        audit_path=audit_path,
        review_path=review_path,
        json_out=json_out,
        md_out=md_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "vvuq_credibility_ledger_report: "
        f"rows={ledger['summary']['row_count']} "
        f"promotion_allowed_count={ledger['promotion_allowed_count']} "
        f"json={_ptr(json_out)} md={_ptr(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
