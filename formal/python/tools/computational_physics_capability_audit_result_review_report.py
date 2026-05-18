from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_ACCEPTS_BOUNDED_NONCLAIM_CLASSIFICATION_"
    "AND_AUTHORIZES_VVUQ_LEDGER_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_AUDIT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_20260515_v0.json"
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


def _archive_or_quarantine_paths(audit: dict[str, Any]) -> list[str]:
    paths: list[str] = []
    for row in audit.get("audit_rows", []):
        for evidence in row.get("evidence_paths", []):
            path = str(evidence.get("path", "")).replace("\\", "/")
            parts = Path(path).parts
            if bool(parts and parts[0] in {"archive", "quarantine"}) or "/quarantine/" in path:
                paths.append(path)
    return sorted(paths)


def _gap_counts(audit: dict[str, Any], field: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in audit.get("audit_rows", []):
        value = str(row.get(field, "missing"))
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def build_result_review(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    audit = _read_json(audit_path)
    summary = dict(audit.get("summary", {}))
    rows = list(audit.get("audit_rows", []))
    archive_or_quarantine_paths = _archive_or_quarantine_paths(audit)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    promotion_allowed_count = int(summary.get("promotion_allowed_count", -1))
    missing_evidence_count = int(summary.get("missing_evidence_count", -1))
    all_promotion_allowed_false = bool(summary.get("all_promotion_allowed_false", False))
    nonclaim_boundary = str(audit.get("non_claim_boundary", ""))

    acceptance_criteria = {
        "consumes_capability_audit": audit.get("audit_id") == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "audit_status_nonclaim": audit.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "authorization_class_preserved": audit.get("authorization_class") == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "promotion_allowed_count_zero": promotion_allowed_count == 0,
        "all_promotion_allowed_false": all_promotion_allowed_false,
        "missing_evidence_count_zero": missing_evidence_count == 0,
        "archive_quarantine_scope_absent": len(archive_or_quarantine_paths) == 0,
        "classification_outcome_nonclaim": str(audit.get("classification_outcome", "")).endswith("WITHOUT_PROMOTION"),
        "nonclaim_boundary_explicit": "no theorem discharge" in nonclaim_boundary,
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }

    accepted = all(acceptance_criteria.values())
    if not accepted:
        next_packet = "BLOCKED_PENDING_CAPABILITY_AUDIT_REMEDIATION"
        next_action = "REMEDIATE_CAPABILITY_AUDIT_RESULT_REVIEW_FAILURE"
    else:
        next_packet = "VVUQ_CREDIBILITY_LEDGER_v0"
        next_action = "PREPARE_VVUQ_CREDIBILITY_LEDGER_AFTER_CAPABILITY_AUDIT_REVIEW"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_audit": {
            "audit_id": audit.get("audit_id"),
            "audit_path": _ptr(audit_path),
            "audit_schema_id": audit.get("schema_id"),
            "audit_row_count": len(rows),
            "audit_classification_outcome": audit.get("classification_outcome"),
        },
        "acceptance_criteria": acceptance_criteria,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID if accepted else "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_BLOCKED",
        "forbidden_effect_status": forbidden_effect_status,
        "scope_confirmation": {
            "promotion_allowed_count": promotion_allowed_count,
            "missing_evidence_count": missing_evidence_count,
            "archive_or_quarantine_path_count": len(archive_or_quarantine_paths),
            "archive_or_quarantine_paths": archive_or_quarantine_paths,
            "whole_repo_inventory_claimed": False,
            "every_python_test_inventory_claimed": False,
            "every_lean_file_inventory_claimed": False,
        },
        "gap_readout": {
            "strongest_gap_pattern": "UQ_DEPTH_AND_VALIDATION_DEPTH_ARE_PRIMARY_NEXT_CREDIBILITY_GAPS",
            "verification_status_counts": _gap_counts(audit, "verification_status"),
            "validation_status_counts": _gap_counts(audit, "validation_status"),
            "uq_status_counts": _gap_counts(audit, "uq_status"),
            "robustness_status_counts": _gap_counts(audit, "robustness_status"),
            "known_limit_status_counts": _gap_counts(audit, "known_limit_status"),
            "falsifier_status_counts": _gap_counts(audit, "falsifier_status"),
        },
        "next_packet": next_packet,
        "next_action": next_action,
        "next_packet_authorization_scope": "PREPARATION_ONLY",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Result review accepts bounded capability classification only; it authorizes VVUQ ledger "
            "preparation only and does not authorize theorem discharge, blocker movement, lane reopen, "
            "Phase 2 authorization, empirical validation claim, seam closure, master-action promotion, "
            "or external-truth claim."
        ),
    }


def write_result_review(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(audit_path=audit_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the computational-physics capability-audit result review.")
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(audit_path=audit_path, out=out, captured_at_utc=str(ns.captured_at_utc))
    print(
        "computational_physics_capability_audit_result_review_report: "
        f"accepted={payload['accepted']} next_packet={payload['next_packet']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
