from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_ACCEPTS_NONCLAIM_ROBUSTNESS_OBLIGATION_PROTOCOL_"
    "AND_AUTHORIZES_REFERENT_REGISTRY_PREPARATION_ONLY"
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
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_20260515_v0.json"
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


def _ids(payload: dict[str, Any], key: str) -> list[str]:
    return [str(row["artifact_id"]) for row in payload.get(key, [])]


def _counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        value = str(row.get(field, "missing"))
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def _all_scans_unexecuted(rows: list[dict[str, Any]]) -> bool:
    return all(row.get("scan_execution_status") == "not_executed_v0" for row in rows)


def _method_debt_visible(rows: list[dict[str, Any]]) -> bool:
    by_id = {str(row["artifact_id"]): row for row in rows}
    for artifact_id in ("C6_CP_NLSE_2D_LANE", "C7_MT01A_ACOUSTIC_METRIC_LANE"):
        row = by_id.get(artifact_id)
        if row is None:
            return False
        if row.get("robustness_applicability") != "simulation_or_numerical_method_surface":
            return False
        if row.get("method_verification_dependency") != "method_debt_visible":
            return False
        if row.get("source_method_applicability") != "numerical_method_applicable":
            return False
        if row.get("source_convergence_status") != "not_registered_v0":
            return False
        if row.get("source_solver_crosscheck_status") != "not_performed":
            return False
    return True


def _uq_limits_visible(rows: list[dict[str, Any]]) -> bool:
    counts = _counts(rows, "uq_dependency")
    return (
        counts.get("uq_not_quantified") == 5
        and counts.get("uq_qualitative") == 2
        and counts.get("uq_partial_quantitative") == 1
    )


def build_result_review(
    *,
    protocol_path: Path = DEFAULT_PROTOCOL_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    protocol = _read_json(protocol_path)
    audit = _read_json(audit_path)
    ledger = _read_json(ledger_path)
    registry = _read_json(registry_path)
    matrix = _read_json(matrix_path)
    rows = list(protocol.get("protocol_rows", []))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    row_ids_match = (
        _ids(protocol, "protocol_rows")
        == _ids(audit, "audit_rows")
        == _ids(ledger, "ledger_rows")
        == _ids(registry, "registry_rows")
        == _ids(matrix, "matrix_rows")
    )

    scan_execution_status_counts = _counts(rows, "scan_execution_status")
    acceptance_criteria = {
        "consumes_sensitivity_robustness_protocol": protocol.get("protocol_id")
        == "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0",
        "protocol_status_nonclaim": protocol.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "authorization_class_preserved": protocol.get("authorization_class")
        == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "protocol_row_count_exact": int(protocol.get("row_count", -1)) == 8,
        "row_ids_match_prior_lineage": row_ids_match,
        "promotion_allowed_count_zero": int(protocol.get("promotion_allowed_count", -1)) == 0,
        "all_promotion_allowed_false": bool(protocol.get("all_promotion_allowed_false", False)),
        "validation_upgrade_count_zero": int(protocol.get("validation_upgrade_count", -1)) == 0,
        "robustness_completion_claim_count_zero": int(
            protocol.get("robustness_completion_claim_count", -1)
        )
        == 0,
        "scan_execution_claim_count_zero": int(protocol.get("scan_execution_claim_count", -1)) == 0,
        "all_scan_execution_status_not_executed_v0": _all_scans_unexecuted(rows),
        "no_numerical_credibility_score": protocol.get("scoring_policy")
        == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "primary_robustness_gap_preserved": protocol.get("primary_robustness_gap")
        == "PERTURBATION_RESOLUTION_SOLVER_TOLERANCE_AND_FAILURE_ENVELOPE_PROTOCOL_NOT_EXECUTED_V0",
        "protocol_scope_preserved": protocol.get("protocol_scope")
        == "DEFINE_ROBUSTNESS_REQUIREMENTS_ONLY_NO_SCAN_EXECUTION_CLAIM",
        "c6_c7_method_debt_visible": _method_debt_visible(rows),
        "uq_limitations_visible": _uq_limits_visible(rows),
        "scan_execution_counts_expected": scan_execution_status_counts == {"not_executed_v0": 8},
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }

    accepted = all(acceptance_criteria.values())
    if accepted:
        next_packet = "REFERENT_REGISTRY_v0"
        next_action = "PREPARE_REFERENT_REGISTRY_AFTER_SENSITIVITY_ROBUSTNESS_PROTOCOL_REVIEW"
        outcome_id = OUTCOME_ID
    else:
        next_packet = "BLOCKED_PENDING_SENSITIVITY_ROBUSTNESS_PROTOCOL_REMEDIATION"
        next_action = "REMEDIATE_SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_FAILURE"
        outcome_id = "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_BLOCKED"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_protocol": {
            "protocol_id": protocol.get("protocol_id"),
            "protocol_path": _ptr(protocol_path),
            "protocol_schema_id": protocol.get("schema_id"),
            "protocol_row_count": len(rows),
            "protocol_preparation_result": protocol.get("preparation_result"),
        },
        "source_lineage": {
            "source_audit": audit.get("audit_id"),
            "source_vvuq_ledger": ledger.get("ledger_id"),
            "source_registry": registry.get("registry_id"),
            "source_matrix": matrix.get("matrix_id"),
            "row_ids_match_prior_lineage": row_ids_match,
        },
        "acceptance_criteria": acceptance_criteria,
        "accepted": accepted,
        "outcome_id": outcome_id,
        "forbidden_effect_status": forbidden_effect_status,
        "scope_confirmation": {
            "promotion_allowed_count": int(protocol.get("promotion_allowed_count", -1)),
            "all_promotion_allowed_false": bool(protocol.get("all_promotion_allowed_false", False)),
            "validation_upgrade_count": int(protocol.get("validation_upgrade_count", -1)),
            "robustness_completion_claim_count": int(
                protocol.get("robustness_completion_claim_count", -1)
            ),
            "scan_execution_claim_count": int(protocol.get("scan_execution_claim_count", -1)),
            "numerical_score_present": "credibility_score" in json.dumps(protocol, sort_keys=True),
            "all_scan_execution_status_not_executed_v0": _all_scans_unexecuted(rows),
        },
        "robustness_gap_confirmation": {
            "primary_robustness_gap": protocol.get("primary_robustness_gap"),
            "protocol_scope": protocol.get("protocol_scope"),
            "robustness_applicability_counts": _counts(rows, "robustness_applicability"),
            "current_robustness_status_counts": _counts(rows, "current_robustness_status"),
            "scan_execution_status_counts": scan_execution_status_counts,
            "uq_dependency_counts": _counts(rows, "uq_dependency"),
            "c6_c7_method_debt_visible": _method_debt_visible(rows),
            "uq_limitations_visible": _uq_limits_visible(rows),
        },
        "next_packet": next_packet,
        "next_action": next_action,
        "next_packet_authorization_scope": "PREPARATION_ONLY",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Result review accepts nonclaim robustness-obligation protocol bookkeeping only; it authorizes "
            "referent registry preparation only and does not authorize scan execution, robustness completion, "
            "theorem discharge, blocker movement, lane reopen, Phase 2 authorization, empirical validation claim, "
            "seam closure, master-action promotion, or external-truth claim."
        ),
    }


def write_result_review(
    *,
    protocol_path: Path = DEFAULT_PROTOCOL_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        protocol_path=protocol_path,
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        matrix_path=matrix_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the sensitivity/robustness protocol result review.")
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL_PATH)
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY_PATH)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    protocol_path = ns.protocol if ns.protocol.is_absolute() else (REPO_ROOT / ns.protocol)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    ledger_path = ns.ledger if ns.ledger.is_absolute() else (REPO_ROOT / ns.ledger)
    registry_path = ns.registry if ns.registry.is_absolute() else (REPO_ROOT / ns.registry)
    matrix_path = ns.matrix if ns.matrix.is_absolute() else (REPO_ROOT / ns.matrix)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        protocol_path=protocol_path,
        audit_path=audit_path,
        ledger_path=ledger_path,
        registry_path=registry_path,
        matrix_path=matrix_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "sensitivity_robustness_protocol_result_review_report: "
        f"accepted={payload['accepted']} next_packet={payload['next_packet']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
