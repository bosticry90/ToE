from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_ACCEPTS_NONCLAIM_KNOWN_LIMIT_BOOKKEEPING_"
    "AND_AUTHORIZES_SENSITIVITY_ROBUSTNESS_PROTOCOL_PREPARATION_ONLY"
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
DEFAULT_OUT = (
    REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0.json"
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

CONSERVATIVE_RECOVERY_STATUSES = {"none", "candidate", "partial", "blocked", "not_applicable"}
PROHIBITED_RECOVERY_STATUSES = {"passed", "validated", "confirmed", "complete", "recovered_complete"}


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ids(payload: dict[str, Any], key: str) -> list[str]:
    return [str(row["artifact_id"]) for row in payload.get(key, [])]


def _counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        value = str(row.get(field, "missing"))
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def _nonconservative_recovery_statuses(rows: list[dict[str, Any]]) -> list[dict[str, str]]:
    nonconservative: list[dict[str, str]] = []
    for row in rows:
        value = str(row.get("matrix_recovery_status"))
        if value not in CONSERVATIVE_RECOVERY_STATUSES or value in PROHIBITED_RECOVERY_STATUSES:
            nonconservative.append({"artifact_id": str(row["artifact_id"]), "matrix_recovery_status": value})
    return nonconservative


def _method_debt_visible(rows: list[dict[str, Any]]) -> bool:
    by_id = {str(row["artifact_id"]): row for row in rows}
    for artifact_id in ("C6_CP_NLSE_2D_LANE", "C7_MT01A_ACOUSTIC_METRIC_LANE"):
        row = by_id.get(artifact_id)
        if row is None:
            return False
        if row.get("source_method_applicability") != "numerical_method_applicable":
            return False
        if row.get("source_convergence_status") != "not_registered_v0":
            return False
        if row.get("source_solver_crosscheck_status") != "not_performed":
            return False
        if row.get("method_verification_dependency") != "method_debt_visible_convergence_mms_or_solver_crosscheck_unresolved_v0":
            return False
    return True


def build_result_review(
    *,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    matrix = _read_json(matrix_path)
    audit = _read_json(audit_path)
    ledger = _read_json(ledger_path)
    registry = _read_json(registry_path)
    rows = list(matrix.get("matrix_rows", []))
    nonconservative_statuses = _nonconservative_recovery_statuses(rows)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    row_ids_match = _ids(matrix, "matrix_rows") == _ids(audit, "audit_rows") == _ids(ledger, "ledger_rows") == _ids(
        registry, "registry_rows"
    )

    acceptance_criteria = {
        "consumes_regime_recovery_matrix": matrix.get("matrix_id") == "REGIME_RECOVERY_MATRIX_v0",
        "matrix_status_nonclaim": matrix.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "authorization_class_preserved": matrix.get("authorization_class") == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "matrix_row_count_exact": int(matrix.get("row_count", -1)) == 8,
        "row_ids_match_prior_lineage": row_ids_match,
        "promotion_allowed_count_zero": int(matrix.get("promotion_allowed_count", -1)) == 0,
        "all_promotion_allowed_false": bool(matrix.get("all_promotion_allowed_false", False)),
        "validation_upgrade_count_zero": int(matrix.get("validation_upgrade_count", -1)) == 0,
        "recovery_completion_claim_count_zero": int(matrix.get("recovery_completion_claim_count", -1)) == 0,
        "no_numerical_credibility_score": matrix.get("scoring_policy") == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "primary_regime_gap_preserved": matrix.get("primary_regime_gap")
        == "KNOWN_LIMIT_PASS_FAIL_CRITERIA_AND_RECOVERY_EVIDENCE_DEPTH_NOT_COMPLETE_V0",
        "conservative_recovery_statuses_preserved": len(nonconservative_statuses) == 0,
        "c6_c7_method_debt_visible": _method_debt_visible(rows),
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }

    accepted = all(acceptance_criteria.values())
    if accepted:
        next_packet = "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0"
        next_action = "PREPARE_SENSITIVITY_ROBUSTNESS_PROTOCOL_AFTER_REGIME_RECOVERY_MATRIX_REVIEW"
        outcome_id = OUTCOME_ID
    else:
        next_packet = "BLOCKED_PENDING_REGIME_RECOVERY_MATRIX_REMEDIATION"
        next_action = "REMEDIATE_REGIME_RECOVERY_MATRIX_RESULT_REVIEW_FAILURE"
        outcome_id = "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_BLOCKED"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_matrix": {
            "matrix_id": matrix.get("matrix_id"),
            "matrix_path": _ptr(matrix_path),
            "matrix_schema_id": matrix.get("schema_id"),
            "matrix_row_count": len(rows),
            "matrix_preparation_result": matrix.get("preparation_result"),
        },
        "source_lineage": {
            "source_audit": audit.get("audit_id"),
            "source_vvuq_ledger": ledger.get("ledger_id"),
            "source_registry": registry.get("registry_id"),
            "row_ids_match_prior_lineage": row_ids_match,
        },
        "acceptance_criteria": acceptance_criteria,
        "accepted": accepted,
        "outcome_id": outcome_id,
        "forbidden_effect_status": forbidden_effect_status,
        "scope_confirmation": {
            "promotion_allowed_count": int(matrix.get("promotion_allowed_count", -1)),
            "all_promotion_allowed_false": bool(matrix.get("all_promotion_allowed_false", False)),
            "validation_upgrade_count": int(matrix.get("validation_upgrade_count", -1)),
            "recovery_completion_claim_count": int(matrix.get("recovery_completion_claim_count", -1)),
            "numerical_score_present": "credibility_score" in json.dumps(matrix, sort_keys=True),
            "nonconservative_recovery_statuses": nonconservative_statuses,
        },
        "regime_gap_confirmation": {
            "primary_regime_gap": matrix.get("primary_regime_gap"),
            "matrix_recovery_status_counts": _counts(rows, "matrix_recovery_status"),
            "regime_recovery_applicability_counts": _counts(rows, "regime_recovery_applicability"),
            "pass_fail_criterion_status_counts": _counts(rows, "pass_fail_criterion_status"),
            "referent_status_counts": _counts(rows, "referent_status"),
            "c6_c7_method_debt_visible": _method_debt_visible(rows),
        },
        "next_packet": next_packet,
        "next_action": next_action,
        "next_packet_authorization_scope": "PREPARATION_ONLY",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Result review accepts nonclaim known-limit and regime-recovery bookkeeping only; it authorizes "
            "sensitivity/robustness protocol preparation only and does not authorize known-limit recovery completion, "
            "theorem discharge, blocker movement, lane reopen, Phase 2 authorization, empirical validation claim, "
            "seam closure, master-action promotion, or external-truth claim."
        ),
    }


def write_result_review(
    *,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        matrix_path=matrix_path,
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the regime-recovery matrix result review.")
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX_PATH)
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    matrix_path = ns.matrix if ns.matrix.is_absolute() else (REPO_ROOT / ns.matrix)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    ledger_path = ns.ledger if ns.ledger.is_absolute() else (REPO_ROOT / ns.ledger)
    registry_path = ns.registry if ns.registry.is_absolute() else (REPO_ROOT / ns.registry)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        matrix_path=matrix_path,
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "regime_recovery_matrix_result_review_report: "
        f"accepted={payload['accepted']} next_packet={payload['next_packet']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
