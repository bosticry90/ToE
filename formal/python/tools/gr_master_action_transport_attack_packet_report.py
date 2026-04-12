from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET_20260412_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    transport_policy = dict(declaration.get("transport_policy", {}))
    ruling_contract = dict(declaration.get("ruling_contract", {}))

    gr_decl_path = REPO_ROOT / str(required_inputs.get("gr_subtarget_declaration", "")).strip()
    gr_report_path = REPO_ROOT / str(required_inputs.get("gr_subtarget_report", "")).strip()
    stop_rule_path = REPO_ROOT / str(required_inputs.get("gr_stop_rule_decision_report", "")).strip()
    row_trend_path = REPO_ROOT / str(required_inputs.get("row_outcome_trend_report", "")).strip()
    ledger_path = REPO_ROOT / str(required_inputs.get("ledger_report", "")).strip()
    master_action_surface_path = REPO_ROOT / str(
        required_inputs.get("master_action_transport_surface_report", "")
    ).strip()

    gr_decl = _read_json(gr_decl_path)
    gr_report = _read_json(gr_report_path)
    stop_rule = _read_json(stop_rule_path)
    row_trend = _read_json(row_trend_path)
    ledger = _read_json(ledger_path)
    master_action_surface = _read_json(master_action_surface_path)

    target_row = str(declaration.get("target_row", "")).strip()
    decl_target_row = str(gr_decl.get("target_row", "")).strip()
    report_inputs = dict(dict(gr_report.get("objective_quality", {})).get("inputs", {}))
    report_target_row = str(report_inputs.get("target_row", "")).strip()

    theorem_gap_delta = int(report_inputs.get("theorem_gap_delta", 0) or 0)
    target_row_success_incremented = bool(report_inputs.get("target_row_success_count_incremented", False))

    row_success_count = int(
        dict(dict(row_trend.get("objective_quality", {})).get("inputs", {}).get("row_outcome_counts", {}))
        .get(target_row, {})
        .get("success", 0)
        or 0
    )

    stop_summary = dict(stop_rule.get("summary", {}))
    stop_decision = str(stop_summary.get("decision", "")).strip()
    reclassification_signal = stop_decision == "DEFER_OR_RECLASSIFY_GR_NEAR_TERM_BLOCKER_BURN_LANE"

    blocker_state_change = str(ledger.get("actual_blocker_state_change", "")).strip()
    blocker_state_token_changed = blocker_state_change not in {"", "NO_DELTA_DETECTED_ROUTE_TO_REWORK"}

    gr_master_action_transport_obligation_declared = bool(
        transport_policy.get("gr_master_action_transport_obligation_declared", False)
    )
    require_reclassification_signal = bool(transport_policy.get("require_reclassification_signal", True))
    require_no_delta_signal = bool(transport_policy.get("require_no_delta_signal", True))

    no_delta_signal = theorem_gap_delta == 0 and not target_row_success_incremented and row_success_count == 0
    scope_match = target_row == decl_target_row == report_target_row

    master_action_surface_present = (
        str(master_action_surface.get("attack_class", "")).strip() == "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS"
    )

    allowed_outcomes = set(ruling_contract.get("allowed_outcomes", []))
    default_outcome = str(ruling_contract.get("default_outcome", "GR_VALID_BUT_NONMOVING")).strip()

    base_preconditions_ok = (
        scope_match
        and master_action_surface_present
        and (not require_reclassification_signal or reclassification_signal)
    )

    if not base_preconditions_ok:
        terminal_outcome = "GR_PATH_FALSIFIED"
        next_action = "STOP_GR_MASTER_ACTION_PATH_AND_REVIEW_SCOPE_OR_PRECONDITIONS"
    elif theorem_gap_delta < 0 or target_row_success_incremented or blocker_state_token_changed:
        terminal_outcome = "GR_BLOCKER_MOVED"
        next_action = "PROMOTE_GR_MASTER_ACTION_ATTACK_AND_CONTINUE_BOUNDED_PROGRAM"
    elif (not require_no_delta_signal or no_delta_signal) and not gr_master_action_transport_obligation_declared:
        terminal_outcome = "GR_MASTER_ACTION_TRANSPORT_REQUIRES_UNDECLARED_STRUCTURE"
        next_action = "DECLARE_ONE_EXPLICIT_GR_MASTER_ACTION_TRANSPORT_OBLIGATION_BEFORE_RETRY"
    else:
        terminal_outcome = "GR_VALID_BUT_NONMOVING"
        next_action = "HOLD_GR_MASTER_ACTION_ATTACK_AND_RESELECT_IF_NEEDED"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_row_scope_match": scope_match,
            "master_action_transport_surface_present": master_action_surface_present,
            "reclassification_signal_present": reclassification_signal,
            "no_delta_signal_present": no_delta_signal,
            "single_terminal_outcome_rule_declared": str(
                ruling_contract.get("single_terminal_outcome_rule", "")
            ).strip() == "EXACTLY_ONE_ALLOWED_GR_MASTER_ACTION_TRANSPORT_OUTCOME",
            "no_loop_rule_declared": str(ruling_contract.get("no_loop_rule", "")).strip()
            == "ONE_GR_MASTER_ACTION_TRANSPORT_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "undeclared_structure_condition_checked": True,
            },
            "inputs": {
                "target_row": target_row,
                "declaration_target_row": decl_target_row,
                "report_target_row": report_target_row,
                "theorem_gap_delta": theorem_gap_delta,
                "target_row_success_incremented": target_row_success_incremented,
                "row_success_count": row_success_count,
                "stop_decision": stop_decision,
                "reclassification_signal": reclassification_signal,
                "blocker_state_change": blocker_state_change,
                "blocker_state_token_changed": blocker_state_token_changed,
                "gr_master_action_transport_obligation_declared": gr_master_action_transport_obligation_declared,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome
                in {
                    "GR_BLOCKER_MOVED",
                    "GR_VALID_BUT_NONMOVING",
                    "GR_MASTER_ACTION_TRANSPORT_REQUIRES_UNDECLARED_STRUCTURE",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row": target_row,
            "next_action": next_action,
            "single_execution_only": bool(transport_policy.get("single_execution_only", True)),
            "single_ruling_only": bool(transport_policy.get("single_ruling_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gr_subtarget_declaration": _ptr(gr_decl_path),
            "gr_subtarget_report": _ptr(gr_report_path),
            "gr_stop_rule_decision_report": _ptr(stop_rule_path),
            "row_outcome_trend_report": _ptr(row_trend_path),
            "ledger_report": _ptr(ledger_path),
            "master_action_transport_surface_report": _ptr(master_action_surface_path),
        },
        "non_claim_boundary": "Repository-local GR master-action transport attack packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate GR master-action transport attack packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "gr_master_action_transport_attack_packet_20260412_v0.json",
    )
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
        "gr_master_action_transport_attack_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
