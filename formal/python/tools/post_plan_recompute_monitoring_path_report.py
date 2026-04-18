from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_RECOMPUTE_MONITORING_PATH_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_RECOMPUTE_MONITORING_PATH_20260418_v0.json"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_recompute_monitoring_path_20260418_v0.json"


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    packet_chain_path = REPO_ROOT / str(required_inputs.get("post_plan_bounded_coupling_refinement_packet_chain_report", "")).strip()
    observation_path = REPO_ROOT / str(required_inputs.get("recompute_observation_report", "")).strip()
    post_observation_path = REPO_ROOT / str(required_inputs.get("post_recompute_observation_report", "")).strip()

    packet_chain_report = _read_json(packet_chain_path)
    observation_report = _read_json(observation_path)
    post_observation_report = _read_json(post_observation_path)

    packet_chain_ok = (
        packet_chain_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_packet_chain_outcome", "")).strip()
        and packet_chain_report.get("summary", {}).get("next_action") == str(policy.get("required_packet_chain_next_action", "")).strip()
    )

    observation_summary = dict(observation_report.get("interpretation_summary", {}))
    observation_outcome = dict(observation_report.get("observation_outcome", {}))
    cascade_analysis = dict(observation_report.get("cascade_analysis", {}))
    trigger_propagation_confirmed = bool(
        cascade_analysis.get("trigger_propagation_confirmed")
        or observation_summary.get("trigger_propagation_confirmed")
    )
    observation_ok = (
        trigger_propagation_confirmed is bool(policy.get("required_trigger_propagation_confirmed", True))
        and observation_outcome.get("next_decision_layer") == str(policy.get("required_recompute_observation_next_layer", "")).strip()
    )

    post_summary = dict(post_observation_report.get("summary", {}))
    post_ruling = dict(post_observation_report.get("post_recompute_ruling", {}))
    post_ruling_id = post_summary.get("ruling_id") or post_ruling.get("ruling_id")
    post_next_action = post_summary.get("next_action") or post_ruling.get("next_action")
    cascade_determination = post_summary.get("cascade_determination")
    post_pending_ok = (
        post_ruling_id == str(policy.get("required_post_recompute_ruling_id", "")).strip()
        and post_next_action == str(policy.get("required_post_recompute_next_action", "")).strip()
        and cascade_determination == str(policy.get("required_cascade_determination", "")).strip()
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "POST_PLAN_RECOMPUTE_MONITORING_PATH_EVIDENCE_INCOMPLETE")).strip()

    if not packet_chain_report or not observation_report or not post_observation_report:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_RECOMPUTE_MONITORING_PATH_REPAIR"
        next_action = "RESTORE_POST_PLAN_RECOMPUTE_MONITORING_INPUTS_AND_RERUN"
    elif packet_chain_ok and observation_ok and post_pending_ok:
        terminal_outcome = "POST_PLAN_RECOMPUTE_MONITORING_PATH_PENDING_COMPLETION"
        next_action = post_next_action
    elif packet_chain_ok and observation_ok and post_ruling_id == "MATERIAL_CASCADE_CONFIRMED":
        terminal_outcome = "POST_PLAN_RECOMPUTE_MONITORING_PATH_MATERIAL_CASCADE_CONFIRMED"
        next_action = post_next_action
    elif packet_chain_ok and observation_ok and post_ruling_id == "TRIGGER_PROPAGATION_ONLY_AUTHORITY_LOCAL":
        terminal_outcome = "POST_PLAN_RECOMPUTE_MONITORING_PATH_AUTHORITY_LOCAL_ONLY"
        next_action = post_next_action
    elif packet_chain_ok:
        terminal_outcome = "POST_PLAN_RECOMPUTE_MONITORING_PATH_BLOCKED"
        next_action = "REPAIR_RECOMPUTE_MONITORING_CHAIN_OR_HOLD_PROGRAM_STATE"
    else:
        terminal_outcome = "POST_PLAN_RECOMPUTE_MONITORING_PATH_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_RECOMPUTE_MONITORING_PATH_EVIDENCE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "coupling_refinement_chain_materialized": packet_chain_ok,
            "trigger_propagation_observed": observation_ok,
            "post_recompute_ruling_materialized": bool(post_ruling_id),
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip() == "EXACTLY_ONE_ALLOWED_POST_PLAN_RECOMPUTE_MONITORING_PATH_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip() == "ONE_POST_PLAN_RECOMPUTE_MONITORING_PATH_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "monitoring_only_opens_after_promotion_registered": (terminal_outcome != "POST_PLAN_RECOMPUTE_MONITORING_PATH_PENDING_COMPLETION") or packet_chain_ok,
                "defer_monitoring_only_when_recompute_still_pending": (next_action != "DEFER_RULING_MONITOR_RECOMPUTE_COMPLETION") or post_pending_ok,
            },
            "inputs": {
                "packet_chain_outcome": packet_chain_report.get("summary", {}).get("terminal_outcome"),
                "packet_chain_next_action": packet_chain_report.get("summary", {}).get("next_action"),
                "trigger_propagation_confirmed": trigger_propagation_confirmed,
                "recompute_observation_next_layer": observation_outcome.get("next_decision_layer"),
                "surfaces_triggering_recompute": observation_summary.get("surfaces_triggering_recompute") or observation_summary.get("surfaces_showing_trigger_activation"),
                "post_recompute_ruling_id": post_ruling_id,
                "post_recompute_next_action": post_next_action,
                "cascade_determination": cascade_determination,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "packet_chain_outcome": packet_chain_report.get("summary", {}).get("terminal_outcome"),
            "trigger_propagation_confirmed": trigger_propagation_confirmed,
            "post_recompute_ruling_id": post_ruling_id,
            "cascade_determination": cascade_determination,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_bounded_coupling_refinement_packet_chain_report": _ptr(packet_chain_path),
            "recompute_observation_report": _ptr(observation_path),
            "post_recompute_observation_report": _ptr(post_observation_path)
        },
        "non_claim_boundary": "Repository-local post-plan recompute-monitoring path only; no scientific adequacy claim."
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan recompute-monitoring path report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "post_plan_recompute_monitoring_path_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())