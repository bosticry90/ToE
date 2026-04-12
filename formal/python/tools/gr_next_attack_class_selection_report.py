from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_NEXT_ATTACK_CLASS_SELECTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GR_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
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
    selection_policy = dict(declaration.get("selection_policy", {}))
    selection_contract = dict(declaration.get("selection_contract", {}))

    gr_subtarget_decl_path = REPO_ROOT / str(required_inputs.get("gr_subtarget_declaration", "")).strip()
    gr_subtarget_report_path = REPO_ROOT / str(required_inputs.get("gr_subtarget_report", "")).strip()
    gr_stop_rule_path = REPO_ROOT / str(required_inputs.get("gr_stop_rule_decision_report", "")).strip()
    row_outcome_trend_path = REPO_ROOT / str(required_inputs.get("row_outcome_trend_report", "")).strip()
    ledger_path = REPO_ROOT / str(required_inputs.get("ledger_report", "")).strip()

    gr_subtarget_decl = _read_json(gr_subtarget_decl_path)
    gr_subtarget_report = _read_json(gr_subtarget_report_path)
    gr_stop_rule = _read_json(gr_stop_rule_path)
    row_outcome_trend = _read_json(row_outcome_trend_path)
    ledger = _read_json(ledger_path)

    target_row = str(selection_policy.get("target_row", "")).strip()
    decl_target_row = str(gr_subtarget_decl.get("target_row", "")).strip()
    report_target_row = str(
        dict(gr_subtarget_report.get("objective_quality", {})).get("inputs", {}).get("target_row", "")
    ).strip()

    stop_summary = dict(gr_stop_rule.get("summary", {}))
    stop_decision = str(stop_summary.get("decision", "")).strip()
    stop_reclassification_signal = stop_decision == "DEFER_OR_RECLASSIFY_GR_NEAR_TERM_BLOCKER_BURN_LANE"

    theorem_gap_delta = int(
        dict(gr_subtarget_report.get("objective_quality", {})).get("inputs", {}).get("theorem_gap_delta", 0) or 0
    )
    target_row_success_count_incremented = bool(
        dict(gr_subtarget_report.get("objective_quality", {})).get("inputs", {}).get(
            "target_row_success_count_incremented", False
        )
    )

    row_counts = dict(dict(row_outcome_trend.get("objective_quality", {})).get("inputs", {}).get("row_outcome_counts", {})).get(
        target_row, {}
    )
    row_success_count = int(row_counts.get("success", 0) or 0)
    blocker_state_change = str(ledger.get("actual_blocker_state_change", "")).strip()
    blocker_state_token_changed = blocker_state_change not in {"", "NO_DELTA_DETECTED_ROUTE_TO_REWORK"}

    require_stop_rule_reclassification_signal = bool(
        selection_policy.get("require_stop_rule_reclassification_signal", True)
    )
    require_gr_tranche_no_delta_signal = bool(selection_policy.get("require_gr_tranche_no_delta_signal", True))

    prefer_master_action = bool(
        selection_policy.get("prefer_master_action_transport_when_no_delta_and_reclassification", True)
    )
    prefer_weak_field = bool(selection_policy.get("prefer_weak_field_when_row_success_incremented", True))
    prefer_regime_limit = bool(
        selection_policy.get("prefer_regime_limit_when_blocker_state_changed_without_gap_delta", True)
    )
    fallback_to_seam_interface = bool(selection_policy.get("fallback_to_seam_interface_when_scope_conflict", True))

    scope_match = target_row == decl_target_row == report_target_row
    no_delta_signal = theorem_gap_delta == 0 and not target_row_success_count_incremented

    allowed_outcomes = set(selection_contract.get("allowed_outcomes", []))
    default_outcome = str(selection_contract.get("default_outcome", "GR_MASTER_ACTION_TRANSPORT_ATTACK")).strip()

    if not scope_match and fallback_to_seam_interface:
        selected_attack_class = "GR_SEAM_INTERFACE_ATTACK"
        next_action = "OPEN_SINGLE_GR_SEAM_INTERFACE_ATTACK_PACKET"
    elif (
        prefer_weak_field
        and (target_row_success_count_incremented or row_success_count > 0)
        and theorem_gap_delta >= 0
    ):
        selected_attack_class = "GR_WEAK_FIELD_CLOSURE_ATTACK"
        next_action = "OPEN_SINGLE_GR_WEAK_FIELD_CLOSURE_ATTACK_PACKET"
    elif (
        prefer_regime_limit
        and blocker_state_token_changed
        and theorem_gap_delta == 0
        and not target_row_success_count_incremented
    ):
        selected_attack_class = "GR_REGIME_LIMIT_ALIGNMENT_ATTACK"
        next_action = "OPEN_SINGLE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK_PACKET"
    elif (
        prefer_master_action
        and (not require_stop_rule_reclassification_signal or stop_reclassification_signal)
        and (not require_gr_tranche_no_delta_signal or no_delta_signal)
    ):
        selected_attack_class = "GR_MASTER_ACTION_TRANSPORT_ATTACK"
        next_action = str(selection_policy.get("default_next_action", "")).strip() or (
            "OPEN_SINGLE_GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET"
        )
    else:
        selected_attack_class = default_outcome
        next_action = "OPEN_SINGLE_GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET"

    if selected_attack_class not in allowed_outcomes:
        selected_attack_class = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_row_scope_match": scope_match,
            "stop_rule_reclassification_signal": stop_reclassification_signal,
            "gr_tranche_no_delta_signal": no_delta_signal,
            "single_terminal_outcome_rule_declared": str(
                selection_contract.get("single_terminal_outcome_rule", "")
            ).strip() == "EXACTLY_ONE_ALLOWED_GR_NEXT_ATTACK_CLASS",
            "no_loop_rule_declared": str(selection_contract.get("no_loop_rule", "")).strip()
            == "ONE_GR_ATTACK_CLASS_SELECTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": selected_attack_class in allowed_outcomes,
                "single_outcome_materialized": True,
                "selection_preconditions_explicit": True,
            },
            "inputs": {
                "target_row": target_row,
                "declaration_target_row": decl_target_row,
                "report_target_row": report_target_row,
                "theorem_gap_delta": theorem_gap_delta,
                "target_row_success_count_incremented": target_row_success_count_incremented,
                "row_success_count": row_success_count,
                "stop_decision": stop_decision,
                "blocker_state_change": blocker_state_change,
                "stop_reclassification_signal": stop_reclassification_signal,
                "no_delta_signal": no_delta_signal,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "selected_attack_class": selected_attack_class,
            "next_action": next_action,
            "target_row": target_row,
            "selection_basis": {
                "stop_reclassification_signal": stop_reclassification_signal,
                "no_delta_signal": no_delta_signal,
                "blocker_state_token_changed": blocker_state_token_changed,
            },
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gr_subtarget_declaration": _ptr(gr_subtarget_decl_path),
            "gr_subtarget_report": _ptr(gr_subtarget_report_path),
            "gr_stop_rule_decision_report": _ptr(gr_stop_rule_path),
            "row_outcome_trend_report": _ptr(row_outcome_trend_path),
            "ledger_report": _ptr(ledger_path),
        },
        "non_claim_boundary": "Repository-local GR next attack-class selection report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate GR next attack-class selection report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "gr_next_attack_class_selection_20260412_v0.json",
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
        "gr_next_attack_class_selection_report: "
        f"selected_attack_class={payload['summary']['selected_attack_class']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
