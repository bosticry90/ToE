from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_CLOSEOUT_DECISION_REPORT_20260417_v0"

DEFAULT_BASELINE_DECISION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_decision_20260417_v0.json"
DEFAULT_REFINEMENT_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json"


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


def build_report(*, baseline_decision_path: Path, refinement_report_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    baseline_decision = _read_json(baseline_decision_path)
    refinement_report = _read_json(refinement_report_path)

    baseline_summary = dict(baseline_decision.get("summary", {}))
    refinement_summary = dict(refinement_report.get("summary", {}))
    refinement_criteria = dict(refinement_report.get("criteria", {}))

    baseline_authorizes_refinement = (
        str(baseline_summary.get("decision", "")).strip() == "REFINE_v0"
        and str(baseline_summary.get("authorized_follow_on", "")).strip() == "ONE_LOCAL_PACKET01_REFINEMENT_ONLY"
    )
    refinement_boundary_preserved = (
        bool(refinement_criteria.get("same_auxiliary_authorization_class", False))
        and bool(refinement_criteria.get("same_packet_level_inconclusive_ceiling", False))
        and bool(refinement_criteria.get("one_refinement_only", False))
        and not bool(refinement_criteria.get("packet02_authorized", False))
        and not bool(refinement_criteria.get("gpu_backend_authorized", False))
        and not bool(refinement_criteria.get("lane_reopen_implication", False))
        and not bool(refinement_criteria.get("blocker_movement_claim", False))
    )

    recommendation = str(refinement_summary.get("refinement_recommendation", "")).strip()
    if not baseline_authorizes_refinement:
        decision = "STOP_PACKET01_FAMILY_v0"
        basis = "BASELINE_DECISION_DID_NOT_AUTHORIZE_SINGLE_REFINEMENT"
        next_action = "STOP_PACKET01_FAMILY_WITH_NO_FURTHER_ACTION"
    elif not refinement_boundary_preserved:
        decision = "RETIRE_REFINEMENT_v0"
        basis = "REFINEMENT_BOUNDARY_OR_NONCLAIM_GUARD_FAILED"
        next_action = "STOP_PACKET01_FAMILY_AND_DROP_REFINEMENT"
    elif recommendation == "RETAIN_REFINEMENT_v0":
        decision = "RETAIN_REFINEMENT_v0"
        basis = "PERTURBATION_WINDOW_TIGHTENING_REDUCED_REGIME_SPAN_WITHOUT_BREAKING_SIGNAL"
        next_action = "STOP_PACKET01_FAMILY_AND_PRESERVE_REFINED_BASELINE"
    elif recommendation == "RETAIN_BASELINE_v0":
        decision = "RETAIN_BASELINE_v0"
        basis = "REFINEMENT_DID_NOT_IMPROVE_BOUNDED_REGIME_DISCIPLINE_OVER_BASELINE"
        next_action = "STOP_PACKET01_FAMILY_AND_PRESERVE_BASELINE"
    elif recommendation == "RETIRE_REFINEMENT_v0":
        decision = "RETIRE_REFINEMENT_v0"
        basis = "REFINEMENT_SIGNAL_DEGRADED_OR_NONCLAIM_BOUNDARY_FAILED"
        next_action = "STOP_PACKET01_FAMILY_AND_DROP_REFINEMENT"
    else:
        decision = "STOP_PACKET01_FAMILY_v0"
        basis = "REFINEMENT_RESULT_NOT_STRONG_ENOUGH_TO_PREFER_BASELINE_OR_REFINEMENT"
        next_action = "STOP_PACKET01_FAMILY_WITH_NO_FURTHER_ACTION"

    return {
        "schema_id": SCHEMA_ID,
        "report_id": "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_CLOSEOUT_DECISION_REPORT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "baseline_authorizes_single_refinement": baseline_authorizes_refinement,
            "refinement_boundary_preserved": refinement_boundary_preserved,
            "packet02_authorized": False,
            "gpu_backend_authorized": False,
            "lane_reopen_implication": False,
            "blocker_movement_claim": False,
        },
        "summary": {
            "decision": decision,
            "decision_basis": basis,
            "next_action": next_action,
            "packet01_family_closed": True,
            "authorized_follow_on": "NONE",
        },
        "source_bundle": {
            "baseline_decision_report": _ptr(baseline_decision_path),
            "refinement_report": _ptr(refinement_report_path),
        },
        "non_claim_boundary": "Repository-local master-action Packet-01 refinement closeout decision report only; no Packet-02 authorization, no GPU migration, no lane reopen, no blocker movement, and no external-truth claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the ToE master-action Packet-01 refinement closeout decision report.")
    parser.add_argument("--baseline-decision", type=Path, default=DEFAULT_BASELINE_DECISION_PATH)
    parser.add_argument("--refinement-report", type=Path, default=DEFAULT_REFINEMENT_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_refinement_closeout_20260417_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    baseline_decision_path = ns.baseline_decision if ns.baseline_decision.is_absolute() else (REPO_ROOT / ns.baseline_decision)
    refinement_report_path = ns.refinement_report if ns.refinement_report.is_absolute() else (REPO_ROOT / ns.refinement_report)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(baseline_decision_path=baseline_decision_path, refinement_report_path=refinement_report_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "toe_master_action_computational_analysis_packet_01_refinement_closeout_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())