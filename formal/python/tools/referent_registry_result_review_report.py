from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "REFERENT_REGISTRY_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "REFERENT_REGISTRY_RESULT_REVIEW_ACCEPTS_NONCLAIM_REFERENT_REGISTRATION_"
    "AND_AUTHORIZES_SIMULATION_MODEL_CARD_TEMPLATE_PREPARATION_ONLY"
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
DEFAULT_REFERENT_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_20260515_v0.json"
)
DEFAULT_OUT = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json"

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


def _all_comparisons_unexecuted(rows: list[dict[str, Any]]) -> bool:
    return all(row.get("comparison_execution_status") == "not_executed_v0" for row in rows)


def _method_debt_visible(rows: list[dict[str, Any]]) -> bool:
    by_id = {str(row["artifact_id"]): row for row in rows}
    for artifact_id in ("C6_CP_NLSE_2D_LANE", "C7_MT01A_ACOUSTIC_METRIC_LANE"):
        row = by_id.get(artifact_id)
        if row is None:
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
    referent_registry_path: Path = DEFAULT_REFERENT_REGISTRY_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    numerical_registry_path: Path = DEFAULT_NUMERICAL_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    protocol_path: Path = DEFAULT_PROTOCOL_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    referent_registry = _read_json(referent_registry_path)
    audit = _read_json(audit_path)
    ledger = _read_json(ledger_path)
    numerical_registry = _read_json(numerical_registry_path)
    matrix = _read_json(matrix_path)
    protocol = _read_json(protocol_path)
    rows = list(referent_registry.get("referent_rows", []))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    row_ids_match = (
        _ids(referent_registry, "referent_rows")
        == _ids(audit, "audit_rows")
        == _ids(ledger, "ledger_rows")
        == _ids(numerical_registry, "registry_rows")
        == _ids(matrix, "matrix_rows")
        == _ids(protocol, "protocol_rows")
    )
    comparison_execution_status_counts = _counts(rows, "comparison_execution_status")

    acceptance_criteria = {
        "consumes_referent_registry": referent_registry.get("registry_id") == "REFERENT_REGISTRY_v0",
        "registry_status_nonclaim": referent_registry.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "authorization_class_preserved": referent_registry.get("authorization_class")
        == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "registry_row_count_exact": int(referent_registry.get("row_count", -1)) == 8,
        "row_ids_match_prior_lineage": row_ids_match,
        "promotion_allowed_count_zero": int(referent_registry.get("promotion_allowed_count", -1)) == 0,
        "all_promotion_allowed_false": bool(referent_registry.get("all_promotion_allowed_false", False)),
        "validation_upgrade_count_zero": int(referent_registry.get("validation_upgrade_count", -1)) == 0,
        "empirical_validation_claim_count_zero": int(
            referent_registry.get("empirical_validation_claim_count", -1)
        )
        == 0,
        "referent_comparison_execution_claim_count_zero": int(
            referent_registry.get("referent_comparison_execution_claim_count", -1)
        )
        == 0,
        "all_comparison_execution_status_not_executed_v0": _all_comparisons_unexecuted(rows),
        "comparison_execution_counts_expected": comparison_execution_status_counts == {"not_executed_v0": 8},
        "primary_referent_gap_preserved": referent_registry.get("primary_referent_gap")
        == "REFERENT_IDENTIFICATION_ALLOWED_USE_AND_UNCERTAINTY_REGISTRATION_INCOMPLETE_V0",
        "registry_scope_preserved": referent_registry.get("registry_scope")
        == "REGISTER_REFERENTS_ONLY_NO_COMPARISON_OR_VALIDATION_EXECUTION_CLAIM",
        "no_numerical_credibility_score": referent_registry.get("scoring_policy")
        == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "c6_c7_method_debt_visible": _method_debt_visible(rows),
        "uq_limitations_visible": _uq_limits_visible(rows),
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }

    accepted = all(acceptance_criteria.values())
    if accepted:
        next_packet = "SIMULATION_MODEL_CARD_TEMPLATE_v0"
        next_action = "PREPARE_SIMULATION_MODEL_CARD_TEMPLATE_AFTER_REFERENT_REGISTRY_REVIEW"
        outcome_id = OUTCOME_ID
    else:
        next_packet = "BLOCKED_PENDING_REFERENT_REGISTRY_REMEDIATION"
        next_action = "REMEDIATE_REFERENT_REGISTRY_RESULT_REVIEW_FAILURE"
        outcome_id = "REFERENT_REGISTRY_RESULT_REVIEW_BLOCKED"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_registry": {
            "registry_id": referent_registry.get("registry_id"),
            "registry_path": _ptr(referent_registry_path),
            "registry_schema_id": referent_registry.get("schema_id"),
            "registry_row_count": len(rows),
            "registry_preparation_result": referent_registry.get("preparation_result"),
        },
        "source_lineage": {
            "source_audit": audit.get("audit_id"),
            "source_vvuq_ledger": ledger.get("ledger_id"),
            "source_numerical_registry": numerical_registry.get("registry_id"),
            "source_matrix": matrix.get("matrix_id"),
            "source_protocol": protocol.get("protocol_id"),
            "row_ids_match_prior_lineage": row_ids_match,
        },
        "acceptance_criteria": acceptance_criteria,
        "accepted": accepted,
        "outcome_id": outcome_id,
        "forbidden_effect_status": forbidden_effect_status,
        "scope_confirmation": {
            "promotion_allowed_count": int(referent_registry.get("promotion_allowed_count", -1)),
            "all_promotion_allowed_false": bool(referent_registry.get("all_promotion_allowed_false", False)),
            "validation_upgrade_count": int(referent_registry.get("validation_upgrade_count", -1)),
            "empirical_validation_claim_count": int(
                referent_registry.get("empirical_validation_claim_count", -1)
            ),
            "referent_comparison_execution_claim_count": int(
                referent_registry.get("referent_comparison_execution_claim_count", -1)
            ),
            "all_comparison_execution_status_not_executed_v0": _all_comparisons_unexecuted(rows),
            "numerical_score_present": "credibility_score" in json.dumps(referent_registry, sort_keys=True),
        },
        "referent_gap_confirmation": {
            "primary_referent_gap": referent_registry.get("primary_referent_gap"),
            "registry_scope": referent_registry.get("registry_scope"),
            "referent_applicability_counts": _counts(rows, "referent_applicability"),
            "referent_type_counts": _counts(rows, "referent_type"),
            "allowed_use_counts": _counts(rows, "allowed_use"),
            "comparison_execution_status_counts": comparison_execution_status_counts,
            "referent_uncertainty_status_counts": _counts(rows, "referent_uncertainty_status"),
            "uq_dependency_counts": _counts(rows, "uq_dependency"),
            "c6_c7_method_debt_visible": _method_debt_visible(rows),
            "uq_limitations_visible": _uq_limits_visible(rows),
        },
        "next_packet": next_packet,
        "next_action": next_action,
        "next_packet_authorization_scope": "PREPARATION_ONLY",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Result review accepts nonclaim referent registration bookkeeping only; it authorizes simulation "
            "model card template preparation only and does not authorize referent comparison execution, empirical "
            "validation claims, theorem discharge, blocker movement, lane reopen, Phase 2 authorization, seam "
            "closure, master-action promotion, or external-truth claim."
        ),
    }


def write_result_review(
    *,
    referent_registry_path: Path = DEFAULT_REFERENT_REGISTRY_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    numerical_registry_path: Path = DEFAULT_NUMERICAL_REGISTRY_PATH,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    protocol_path: Path = DEFAULT_PROTOCOL_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        referent_registry_path=referent_registry_path,
        audit_path=audit_path,
        ledger_path=ledger_path,
        numerical_registry_path=numerical_registry_path,
        matrix_path=matrix_path,
        protocol_path=protocol_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the referent registry result review.")
    parser.add_argument("--referent-registry", type=Path, default=DEFAULT_REFERENT_REGISTRY_PATH)
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--numerical-registry", type=Path, default=DEFAULT_NUMERICAL_REGISTRY_PATH)
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX_PATH)
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    referent_registry_path = (
        ns.referent_registry if ns.referent_registry.is_absolute() else (REPO_ROOT / ns.referent_registry)
    )
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    ledger_path = ns.ledger if ns.ledger.is_absolute() else (REPO_ROOT / ns.ledger)
    numerical_registry_path = (
        ns.numerical_registry if ns.numerical_registry.is_absolute() else (REPO_ROOT / ns.numerical_registry)
    )
    matrix_path = ns.matrix if ns.matrix.is_absolute() else (REPO_ROOT / ns.matrix)
    protocol_path = ns.protocol if ns.protocol.is_absolute() else (REPO_ROOT / ns.protocol)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        referent_registry_path=referent_registry_path,
        audit_path=audit_path,
        ledger_path=ledger_path,
        numerical_registry_path=numerical_registry_path,
        matrix_path=matrix_path,
        protocol_path=protocol_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "referent_registry_result_review_report: "
        f"accepted={payload['accepted']} next_packet={payload['next_packet']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
