from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "BROADER_SEAM_PACKAGE_REDESIGN_DECISION_20260411_v0"

DEFAULT_TRANCHE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "broader_seam_package_redesign_tranche_report_20260411_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, tranche_report_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    tranche = _read_json(tranche_report_path)

    summary = tranche.get("summary", {})
    packet_outcome = str(summary.get("packet_outcome", "INCONCLUSIVE_TARGET_SEAM_PACKAGE_MAPPING_MISSING"))
    blocker_movement = bool(summary.get("blocker_facing_movement_observed", False))

    if blocker_movement:
        decision = "BROADER_SEAM_REDESIGN_PRODUCTIVE"
        next_action = "CONTINUE_SEAM_REDESIGN_WITH_BLOCKER_REDUCTION_FOCUS"
    else:
        decision = "BROADER_SEAM_REDESIGN_NONPRODUCTIVE_IN_BOUNDED_TRANCHE"
        next_action = "ESCALATE_TO_NEXT_ATTACK_CLASS_EXTERNAL_DISCRIMINATIVE_BENCHMARK_PROGRAM"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "tranche_report_present": tranche_report_path.exists(),
            "packet_outcome_materialized": packet_outcome != "",
            "bounded_decision_materialized": True,
        },
        "summary": {
            "decision": decision,
            "packet_outcome": packet_outcome,
            "blocker_facing_movement_observed": blocker_movement,
            "next_action": next_action,
            "next_attack_class_if_escalated": "EXTERNAL_DISCRIMINATIVE_BENCHMARK_PROGRAM",
        },
        "source_bundle": {
            "tranche_report": _ptr(tranche_report_path),
        },
        "non_claim_boundary": "Repository-local broader seam package redesign decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate broader seam package redesign decision report.")
    parser.add_argument("--tranche-report", type=Path, default=DEFAULT_TRANCHE_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "broader_seam_package_redesign_decision_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    tranche_report_path = ns.tranche_report if ns.tranche_report.is_absolute() else (REPO_ROOT / ns.tranche_report)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(tranche_report_path=tranche_report_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"broader_seam_package_redesign_decision_report: decision={payload['summary']['decision']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
