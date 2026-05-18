from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_ACCEPTS_NONCLAIM_CREDIBILITY_BOOKKEEPING_"
    "AND_AUTHORIZES_NUMERICAL_METHOD_VERIFICATION_REGISTRY_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
DEFAULT_AUDIT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_20260515_v0.json"
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


def _source_audit_by_id(audit: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(row["artifact_id"]): row for row in audit.get("audit_rows", [])}


def _validation_upgrades(ledger: dict[str, Any], audit: dict[str, Any]) -> list[dict[str, str]]:
    audit_by_id = _source_audit_by_id(audit)
    upgrades: list[dict[str, str]] = []
    for row in ledger.get("ledger_rows", []):
        artifact_id = str(row["artifact_id"])
        source = audit_by_id.get(artifact_id, {})
        if str(row.get("validation_status")) != str(source.get("validation_status")):
            upgrades.append(
                {
                    "artifact_id": artifact_id,
                    "source_validation_status": str(source.get("validation_status")),
                    "ledger_validation_status": str(row.get("validation_status")),
                }
            )
    return upgrades


def build_result_review(
    *,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    ledger = _read_json(ledger_path)
    audit = _read_json(audit_path)
    ledger_ids = _ids(ledger, "ledger_rows")
    audit_ids = _ids(audit, "audit_rows")
    validation_upgrades = _validation_upgrades(ledger, audit)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_vvuq_ledger": ledger.get("ledger_id") == "VVUQ_CREDIBILITY_LEDGER_v0",
        "ledger_status_nonclaim": ledger.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "authorization_class_preserved": ledger.get("authorization_class") == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "ledger_row_count_exact": int(ledger.get("summary", {}).get("row_count", -1)) == 8,
        "source_audit_row_count_exact": int(ledger.get("source_audit_row_count", -1)) == 8,
        "row_ids_match_capability_audit": ledger_ids == audit_ids,
        "promotion_allowed_count_zero": int(ledger.get("promotion_allowed_count", -1)) == 0,
        "all_promotion_allowed_false": bool(ledger.get("all_promotion_allowed_false", False)),
        "no_numerical_credibility_score": ledger.get("scoring_policy") == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "no_validation_status_upgrade": len(validation_upgrades) == 0,
        "primary_gap_preserved": ledger.get("primary_gap_pattern")
        == "UQ_DEPTH_AND_VALIDATION_DEPTH_ARE_PRIMARY_NEXT_CREDIBILITY_GAPS",
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }

    accepted = all(acceptance_criteria.values())
    if accepted:
        next_packet = "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0"
        next_action = "PREPARE_NUMERICAL_METHOD_VERIFICATION_REGISTRY_AFTER_VVUQ_LEDGER_REVIEW"
        outcome_id = OUTCOME_ID
    else:
        next_packet = "BLOCKED_PENDING_VVUQ_LEDGER_REMEDIATION"
        next_action = "REMEDIATE_VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_FAILURE"
        outcome_id = "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_BLOCKED"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_ledger": {
            "ledger_id": ledger.get("ledger_id"),
            "ledger_path": _ptr(ledger_path),
            "ledger_schema_id": ledger.get("schema_id"),
            "ledger_row_count": len(ledger.get("ledger_rows", [])),
            "ledger_preparation_result": ledger.get("preparation_result"),
        },
        "source_audit": {
            "audit_id": audit.get("audit_id"),
            "audit_path": _ptr(audit_path),
            "audit_row_count": len(audit.get("audit_rows", [])),
        },
        "acceptance_criteria": acceptance_criteria,
        "accepted": accepted,
        "outcome_id": outcome_id,
        "forbidden_effect_status": forbidden_effect_status,
        "scope_confirmation": {
            "promotion_allowed_count": int(ledger.get("promotion_allowed_count", -1)),
            "all_promotion_allowed_false": bool(ledger.get("all_promotion_allowed_false", False)),
            "validation_upgrade_count": len(validation_upgrades),
            "validation_upgrades": validation_upgrades,
            "numerical_score_present": "credibility_score" in json.dumps(ledger, sort_keys=True),
        },
        "gap_confirmation": {
            "primary_gap_pattern": ledger.get("primary_gap_pattern"),
            "results_uncertainty_counts": ledger.get("summary", {}).get("results_uncertainty_counts", {}),
            "validation_status_counts": ledger.get("summary", {}).get("validation_status_counts", {}),
        },
        "next_packet": next_packet,
        "next_action": next_action,
        "next_packet_authorization_scope": "PREPARATION_ONLY",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Result review accepts nonclaim VVUQ credibility bookkeeping only; it authorizes numerical-method "
            "verification registry preparation only and does not authorize theorem discharge, blocker movement, "
            "lane reopen, Phase 2 authorization, empirical validation claim, seam closure, master-action promotion, "
            "or external-truth claim."
        ),
    }


def write_result_review(
    *,
    ledger_path: Path = DEFAULT_LEDGER_PATH,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(ledger_path=ledger_path, audit_path=audit_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the VVUQ credibility-ledger result review.")
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    ledger_path = ns.ledger if ns.ledger.is_absolute() else (REPO_ROOT / ns.ledger)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        ledger_path=ledger_path,
        audit_path=audit_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "vvuq_credibility_ledger_result_review_report: "
        f"accepted={payload['accepted']} next_packet={payload['next_packet']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
