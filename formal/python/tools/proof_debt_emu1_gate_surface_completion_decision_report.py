from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_EMU1_GATE_SURFACE_COMPLETION_DECISION_20260411_v0"

DEFAULT_TRANCHE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_emu1_gate_surface_completion_tranche_report_20260411_v0.json"
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
    outcome = str(summary.get("packet_outcome", "EMU1_GATE_SURFACE_INSUFFICIENT_OR_UNWIRED"))

    if outcome == "EMU1_GATE_SURFACE_COMPLETED_AND_RERUN_READY":
        decision = "NECESSARY_BUT_INSUFFICIENT_PENDING_ONE_RERUN"
        next_action = "RERUN_PROOF_DEBT_CLUSTER_ONCE_ON_MERITS"
    else:
        decision = "REPRIORITIZE_CLUSTER"
        next_action = "REPRIORITIZE_CLUSTER_INSUFFICIENT_INFRASTRUCTURE_LEVERAGE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "tranche_report_present": tranche_report_path.exists(),
            "outcome_materialized": outcome != "",
            "bounded_decision_materialized": True,
        },
        "summary": {
            "decision": decision,
            "packet_outcome": outcome,
            "next_action": next_action,
        },
        "source_bundle": {
            "tranche_report": _ptr(tranche_report_path),
        },
        "non_claim_boundary": "Repository-local EM-U1 gate-surface completion decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate EM-U1 gate-surface completion decision report.")
    parser.add_argument("--tranche-report", type=Path, default=DEFAULT_TRANCHE_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_emu1_gate_surface_completion_decision_20260411_v0.json",
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
    print(
        "proof_debt_emu1_gate_surface_completion_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
