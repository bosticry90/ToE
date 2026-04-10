from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_PROMOTION_READINESS_ACTION_20260410_v0"

READINESS_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_PROMOTION_READINESS_SCORE_20260410_v0.md"
READINESS_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_promotion_readiness_score_20260410_v0.json"
OWNER_MAP_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json"
BLOCKER_CLOSURE_MAP_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _action_rules() -> dict[str, dict[str, Any]]:
    return {
        "READY": {
            "promotion_allowed": True,
            "required_owner_signoff": ["primary_owner"],
            "allowed_tranche_classes": ["PROMOTION", "ADVANCEMENT", "MAINTENANCE"],
            "exception_required": False,
            "required_exception_artifact": None,
            "action_summary": "PROMOTION_ALLOWED_PRIMARY_OWNER_SIGNOFF",
        },
        "CONDITIONAL": {
            "promotion_allowed": True,
            "required_owner_signoff": ["primary_owner", "secondary_owner"],
            "allowed_tranche_classes": ["LIMITED_PROMOTION", "MAINTENANCE", "BLOCKER_REDUCTION"],
            "exception_required": False,
            "required_exception_artifact": None,
            "action_summary": "LIMITED_PROMOTION_ALLOWED_DUAL_OWNER_SIGNOFF",
        },
        "WATCH": {
            "promotion_allowed": False,
            "required_owner_signoff": ["primary_owner", "secondary_owner"],
            "allowed_tranche_classes": ["MAINTENANCE", "BLOCKER_REDUCTION"],
            "exception_required": True,
            "required_exception_artifact": "formal/docs/release/GOVERNANCE_PROMOTION_EXCEPTION_WATCH_20260410_v0.md",
            "action_summary": "PROMOTION_BLOCKED_EXCEPTION_ARTIFACT_REQUIRED",
        },
        "BLOCKED": {
            "promotion_allowed": False,
            "required_owner_signoff": ["primary_owner", "secondary_owner", "governance_core"],
            "allowed_tranche_classes": ["BLOCKER_REDUCTION"],
            "exception_required": True,
            "required_exception_artifact": "formal/docs/release/GOVERNANCE_PROMOTION_EXCEPTION_BLOCKED_20260410_v0.md",
            "action_summary": "PROMOTION_HARD_BLOCKED_GOVERNANCE_CORE_REVIEW_REQUIRED",
        },
    }


def build_action_report(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    readiness = _read_json(READINESS_REPORT_PATH)
    owner_map = _read_json(OWNER_MAP_PATH)
    blocker_map = _read_json(BLOCKER_CLOSURE_MAP_PATH)

    readiness_score = readiness.get("score", {}).get("readiness_score_0_to_100")
    readiness_status = str(readiness.get("score", {}).get("readiness_status", "")).strip()

    rules = _action_rules()
    if readiness_status not in rules:
        raise ValueError(f"Unexpected readiness status '{readiness_status}' in {READINESS_REPORT_PATH}")

    selected = rules[readiness_status]
    owner_rows = owner_map.get("rows", [])
    if not isinstance(owner_rows, list):
        owner_rows = []

    blocker_rows = blocker_map.get("mappings", [])
    if not isinstance(blocker_rows, list):
        blocker_rows = []

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "readiness_input": {
            "score": readiness_score,
            "status": readiness_status,
            "status_rule": "READY>=85; CONDITIONAL>=65; WATCH>=45; else BLOCKED",
            "source_report": str(READINESS_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "status_action_rules": rules,
        "current_action": {
            "status": readiness_status,
            "promotion_allowed": selected["promotion_allowed"],
            "required_owner_signoff": selected["required_owner_signoff"],
            "allowed_tranche_classes": selected["allowed_tranche_classes"],
            "exception_required": selected["exception_required"],
            "required_exception_artifact": selected["required_exception_artifact"],
            "action_summary": selected["action_summary"],
        },
        "coverage_context": {
            "owner_rows_total": len(owner_rows),
            "blocker_closure_rows_total": len(blocker_rows),
            "missing_owner_rows": blocker_map.get("missing_owner_rows", []),
        },
        "source_bundle": {
            "readiness_declaration": str(READINESS_DECLARATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "readiness_report": str(READINESS_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "closure_owner_map": str(OWNER_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "blocker_closure_map_report": str(BLOCKER_CLOSURE_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "non_claim_boundary": "This readiness-action policy is a repository-local governance control artifact and does not assert scientific adequacy.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate governance readiness-action policy report from readiness score.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_promotion_readiness_action_20260410_v0.json",
        help="Output path for readiness-action policy JSON.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override (e.g. 2026-04-10T00:00:00Z).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    output_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_action_report(output_path=output_path, captured_at_utc=ns.captured_at_utc)
    print(
        "governance_promotion_readiness_action: "
        f"status={payload['current_action']['status']} "
        f"promotion_allowed={payload['current_action']['promotion_allowed']} "
        f"out={output_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
