from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_FRESHNESS_SNAPSHOT_20260410_v0"

RUNTIME_BASELINE_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_runtime_baseline_20260410_v0.json"
ARTIFACT_GROWTH_SNAPSHOT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_artifact_growth_snapshot_20260410_v0.json"
BLOCKER_CLOSURE_MAP_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
PROMOTION_READINESS_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_promotion_readiness_score_20260410_v0.json"
PROMOTION_ACTION_POLICY_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_promotion_readiness_action_20260410_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_now(captured_at_utc: str | None) -> datetime:
    if captured_at_utc:
        return datetime.strptime(captured_at_utc, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    return datetime.now(timezone.utc)


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _captured_datetime(payload: dict[str, Any], path: Path) -> datetime:
    captured = payload.get("captured_at_utc")
    if not isinstance(captured, str) or not captured:
        raise ValueError(f"Missing captured_at_utc in {path}")
    return datetime.strptime(captured, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


def _source_record(*, path: Path, payload: dict[str, Any], now: datetime, max_age_seconds: int) -> dict[str, Any]:
    captured = _captured_datetime(payload, path)
    age_seconds = int((now - captured).total_seconds())
    is_fresh = age_seconds <= max_age_seconds
    return {
        "report_pointer": str(path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "captured_at_utc": captured.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "age_seconds": age_seconds,
        "max_age_seconds": max_age_seconds,
        "is_fresh": is_fresh,
    }


def build_freshness_snapshot(*, output_path: Path, captured_at_utc: str | None, max_age_seconds: int) -> dict[str, Any]:
    now = _resolve_now(captured_at_utc)

    runtime_payload = _read_json(RUNTIME_BASELINE_REPORT_PATH)
    growth_payload = _read_json(ARTIFACT_GROWTH_SNAPSHOT_PATH)
    blocker_payload = _read_json(BLOCKER_CLOSURE_MAP_REPORT_PATH)
    readiness_payload = _read_json(PROMOTION_READINESS_REPORT_PATH)
    action_payload = _read_json(PROMOTION_ACTION_POLICY_REPORT_PATH)

    sources = {
        "runtime_baseline": _source_record(path=RUNTIME_BASELINE_REPORT_PATH, payload=runtime_payload, now=now, max_age_seconds=max_age_seconds),
        "artifact_growth_snapshot": _source_record(path=ARTIFACT_GROWTH_SNAPSHOT_PATH, payload=growth_payload, now=now, max_age_seconds=max_age_seconds),
        "blocker_closure_map": _source_record(path=BLOCKER_CLOSURE_MAP_REPORT_PATH, payload=blocker_payload, now=now, max_age_seconds=max_age_seconds),
        "promotion_readiness": _source_record(path=PROMOTION_READINESS_REPORT_PATH, payload=readiness_payload, now=now, max_age_seconds=max_age_seconds),
        "promotion_action_policy": _source_record(path=PROMOTION_ACTION_POLICY_REPORT_PATH, payload=action_payload, now=now, max_age_seconds=max_age_seconds),
    }

    stale_inputs = [key for key, value in sources.items() if not value["is_fresh"]]
    all_fresh = len(stale_inputs) == 0

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "policy": {
            "max_age_seconds": max_age_seconds,
            "stale_input_effect": "READINESS_INVALID_AND_PROMOTION_NOT_ELIGIBLE",
        },
        "sources": sources,
        "freshness_summary": {
            "all_required_inputs_fresh": all_fresh,
            "stale_inputs": stale_inputs,
            "freshness_status": "FRESH" if all_fresh else "STALE_INPUTS_PRESENT",
            "readiness_inputs_valid": all_fresh,
            "promotion_eligibility_from_freshness": all_fresh,
        },
        "non_claim_boundary": "This freshness snapshot is a repository-local governance control artifact and does not assert scientific adequacy.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate governance freshness snapshot for audit packet dependencies.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_freshness_snapshot_20260410_v0.json",
        help="Output path for freshness snapshot report JSON.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override (e.g. 2026-04-10T00:00:00Z).",
    )
    parser.add_argument(
        "--max-age-seconds",
        type=int,
        default=86400,
        help="Maximum permitted age for required inputs before staleness is triggered.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    output_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_freshness_snapshot(
        output_path=output_path,
        captured_at_utc=ns.captured_at_utc,
        max_age_seconds=ns.max_age_seconds,
    )
    print(
        "governance_freshness_snapshot: "
        f"status={payload['freshness_summary']['freshness_status']} "
        f"stale_inputs={len(payload['freshness_summary']['stale_inputs'])} "
        f"out={output_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
