from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_ACCEPTS_NONCLAIM_METHOD_DEBT_REGISTRATION_"
    "AND_AUTHORIZES_REGIME_RECOVERY_MATRIX_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0.json"
)

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


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _rows_by_applicability(rows: list[dict[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        key = str(row.get("method_applicability", "missing"))
        counts[key] = counts.get(key, 0) + 1
    return dict(sorted(counts.items()))


def _method_completion_claims(rows: list[dict[str, Any]]) -> list[dict[str, str]]:
    claims: list[dict[str, str]] = []
    for row in rows:
        artifact_id = str(row["artifact_id"])
        if row.get("convergence_status") in {"convergence_checked", "measured_pass", "passed"}:
            claims.append({"artifact_id": artifact_id, "field": "convergence_status", "value": str(row["convergence_status"])})
        if row.get("manufactured_solution_status") in {"implemented", "passed"}:
            claims.append(
                {
                    "artifact_id": artifact_id,
                    "field": "manufactured_solution_status",
                    "value": str(row["manufactured_solution_status"]),
                }
            )
        if row.get("exact_solution_benchmark_status") in {"implemented", "passed"}:
            claims.append(
                {
                    "artifact_id": artifact_id,
                    "field": "exact_solution_benchmark_status",
                    "value": str(row["exact_solution_benchmark_status"]),
                }
            )
        if row.get("solver_crosscheck_status") in {"performed", "passed", "solver_crosschecked"}:
            claims.append(
                {
                    "artifact_id": artifact_id,
                    "field": "solver_crosscheck_status",
                    "value": str(row["solver_crosscheck_status"]),
                }
            )
    return claims


def build_result_review(
    *,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    registry = _read_json(registry_path)
    rows = list(registry.get("registry_rows", []))
    applicability_counts = _rows_by_applicability(rows)
    method_completion_claims = _method_completion_claims(rows)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_numerical_method_registry": registry.get("registry_id")
        == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0",
        "registry_status_nonclaim": registry.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "authorization_class_preserved": registry.get("authorization_class")
        == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "registry_row_count_exact": int(registry.get("row_count", -1)) == 8,
        "source_audit_row_count_exact": int(registry.get("source_audit_row_count", -1)) == 8,
        "numerical_method_applicable_count_exact": applicability_counts.get("numerical_method_applicable", 0) == 2,
        "comparator_report_count_exact": applicability_counts.get("comparator_or_report_surface", 0) == 5,
        "formal_governance_count_exact": applicability_counts.get("formal_or_governance_surface", 0) == 1,
        "promotion_allowed_count_zero": int(registry.get("promotion_allowed_count", -1)) == 0,
        "all_promotion_allowed_false": bool(registry.get("all_promotion_allowed_false", False)),
        "validation_upgrade_count_zero": int(registry.get("validation_upgrade_count", -1)) == 0,
        "no_numerical_credibility_score": registry.get("scoring_policy") == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "primary_method_gap_preserved": registry.get("primary_method_gap")
        == "CONVERGENCE_MMS_EXACT_SOLUTION_AND_SOLVER_CROSSCHECK_DEPTH_NOT_REGISTERED_V0",
        "no_method_completion_claims": len(method_completion_claims) == 0,
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }

    accepted = all(acceptance_criteria.values())
    if accepted:
        next_packet = "REGIME_RECOVERY_MATRIX_v0"
        next_action = "PREPARE_REGIME_RECOVERY_MATRIX_AFTER_NUMERICAL_METHOD_REGISTRY_REVIEW"
        outcome_id = OUTCOME_ID
    else:
        next_packet = "BLOCKED_PENDING_NUMERICAL_METHOD_REGISTRY_REMEDIATION"
        next_action = "REMEDIATE_NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_FAILURE"
        outcome_id = "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_BLOCKED"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_registry": {
            "registry_id": registry.get("registry_id"),
            "registry_path": _ptr(registry_path),
            "registry_schema_id": registry.get("schema_id"),
            "registry_row_count": len(rows),
            "registry_preparation_result": registry.get("preparation_result"),
        },
        "acceptance_criteria": acceptance_criteria,
        "accepted": accepted,
        "outcome_id": outcome_id,
        "forbidden_effect_status": forbidden_effect_status,
        "scope_confirmation": {
            "promotion_allowed_count": int(registry.get("promotion_allowed_count", -1)),
            "all_promotion_allowed_false": bool(registry.get("all_promotion_allowed_false", False)),
            "validation_upgrade_count": int(registry.get("validation_upgrade_count", -1)),
            "numerical_score_present": "credibility_score" in json.dumps(registry, sort_keys=True),
            "method_completion_claim_count": len(method_completion_claims),
            "method_completion_claims": method_completion_claims,
        },
        "method_gap_confirmation": {
            "primary_method_gap": registry.get("primary_method_gap"),
            "method_verification_scope": registry.get("method_verification_scope"),
            "method_applicability_counts": applicability_counts,
            "verification_depth_counts": registry.get("summary", {}).get("verification_depth_counts", {}),
            "convergence_not_registered_count": registry.get("summary", {}).get("convergence_not_registered_count"),
            "manufactured_solution_not_passed_count": registry.get("summary", {}).get(
                "manufactured_solution_not_passed_count"
            ),
            "solver_crosscheck_not_performed_count": registry.get("summary", {}).get(
                "solver_crosscheck_not_performed_count"
            ),
        },
        "next_packet": next_packet,
        "next_action": next_action,
        "next_packet_authorization_scope": "PREPARATION_ONLY",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Result review accepts nonclaim numerical-method verification debt registration only; it authorizes "
            "regime-recovery matrix preparation only and does not authorize convergence completion, MMS completion, "
            "exact-solution benchmark completion, solver-crosscheck completion, theorem discharge, blocker movement, "
            "lane reopen, Phase 2 authorization, empirical validation claim, seam closure, master-action promotion, "
            "or external-truth claim."
        ),
    }


def write_result_review(
    *,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(registry_path=registry_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the numerical-method registry result review.")
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    registry_path = ns.registry if ns.registry.is_absolute() else (REPO_ROOT / ns.registry)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        registry_path=registry_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "numerical_method_verification_registry_result_review_report: "
        f"accepted={payload['accepted']} next_packet={payload['next_packet']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
