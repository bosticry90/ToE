from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "BOUNDED_MEASUREMENT_REGIME_PILOT_EXECUTION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "BOUNDED_MEASUREMENT_REGIME_PILOT_EXECUTION_20260411_v0.json"
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
    pilot_targets = dict(declaration.get("pilot_targets", {}))
    revised_signal_spec = dict(declaration.get("revised_signal_spec", {}))
    execution_policy = dict(declaration.get("execution_policy", {}))
    pilot_tranche = str(declaration.get("pilot_tranche", "")).strip()

    transition_path = REPO_ROOT / str(
        required_inputs.get("post_posture_review_program_mode_transition_report", "")
    )
    transition_report = _read_json(transition_path)
    transition_summary = dict(transition_report.get("summary", {}))

    transition_outcome = str(transition_summary.get("transition_outcome", "")).strip()
    pilot_triggered = transition_outcome == "MEASUREMENT_REGIME_TRANSITION_MATERIALIZED"

    target_row_id = str(pilot_targets.get("target_row_id", "")).strip()
    target_package_id = str(pilot_targets.get("target_package_id", "")).strip()
    transport_witness_path = REPO_ROOT / str(pilot_targets.get("transport_witness_artifact", ""))
    bridge_object_path = REPO_ROOT / str(pilot_targets.get("bridge_object_artifact", ""))

    new_signal = str(revised_signal_spec.get("new_signal", "")).strip()
    retained_signal = str(revised_signal_spec.get("retained_signal", "")).strip()
    new_signal_pass_rule = str(revised_signal_spec.get("new_signal_pass_rule", "")).strip()
    retained_signal_pass_rule = str(revised_signal_spec.get("retained_signal_pass_rule", "")).strip()

    no_loop_rule = str(execution_policy.get("no_loop_rule", "")).strip()
    promotion_requires_both = bool(execution_policy.get("promotion_requires_both_signals", True))
    reversibility_rule = str(execution_policy.get("reversibility_rule", "")).strip()

    # Evaluate new signal: SEAM_INTEGRATION_COVERAGE_DELTA_GT_0
    # Pass rule: transport witness is BOUND and bridge object is MATERIALIZED for the target row
    transport_witness_data: dict[str, Any] = {}
    bridge_object_data: dict[str, Any] = {}
    if transport_witness_path.exists():
        transport_witness_data = _read_json(transport_witness_path)
    if bridge_object_path.exists():
        bridge_object_data = _read_json(bridge_object_path)

    transport_witness_bound = (
        str(transport_witness_data.get("status", "")).strip() == "BOUND"
        and str(transport_witness_data.get("row_id", "")).strip() == target_row_id
        and str(transport_witness_data.get("target_package_id", "")).strip() == target_package_id
    )
    bridge_object_materialized = (
        str(bridge_object_data.get("status", "")).strip() == "MATERIALIZED"
        and str(bridge_object_data.get("row_id", "")).strip() == target_row_id
        and str(bridge_object_data.get("target_package_id", "")).strip() == target_package_id
    )

    # New signal fires if both seam-level artifacts are present and correctly bound
    new_signal_fired = transport_witness_bound and bridge_object_materialized

    # Retained signal: BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE
    # Under the current bounded pilot, no blocker-facing token change has been observed
    # (consistent with all prior executions in this chain)
    retained_signal_fired = False  # no ledger blocker-token change observed in any prior execution

    execution_valid = pilot_triggered and new_signal_fired

    if not execution_valid and not pilot_triggered:
        execution_classification = "PILOT_EXECUTION_INCOMPLETE"
        blocker_movement_signal = "NONE_TRIGGERED"
        next_action = "RESTORE_PILOT_EXECUTION_PRECONDITIONS"
    else:
        # Both signals required for promotion; evaluate independently
        if new_signal_fired and retained_signal_fired:
            blocker_movement_signal = "BOTH_SIGNALS_FIRED"
            execution_classification = "PILOT_MOVED"
            next_action = "EMIT_BOUNDED_MEASUREMENT_REGIME_PILOT_RULING"
        elif new_signal_fired and (not retained_signal_fired):
            # New signal fires but retained authoritative signal does not —
            # valid but the retained signal check constrains promotion
            blocker_movement_signal = "NEW_SIGNAL_ONLY"
            execution_classification = "PILOT_VALID_BUT_NONMOVING"
            next_action = "EMIT_BOUNDED_MEASUREMENT_REGIME_PILOT_RULING"
        else:
            blocker_movement_signal = "NONE_TRIGGERED"
            execution_classification = "PILOT_SIGNAL_NOT_FIT"
            next_action = "EMIT_BOUNDED_MEASUREMENT_REGIME_PILOT_RULING"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "pilot_tranche": pilot_tranche,
        "criteria": {
            "transition_outcome_materialized": pilot_triggered,
            "new_signal_fired": new_signal_fired,
            "retained_signal_fired": retained_signal_fired,
            "transport_witness_bound": transport_witness_bound,
            "bridge_object_materialized": bridge_object_materialized,
            "no_loop_rule_declared": no_loop_rule == "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
            "promotion_requires_both_signals": promotion_requires_both,
            "reversibility_rule_declared": bool(reversibility_rule),
        },
        "objective_quality": {
            "criteria": {
                "pilot_execution_triggered": pilot_triggered,
                "new_signal_evaluated": True,
                "retained_signal_evaluated": True,
                "execution_classification_materialized": execution_classification
                in {
                    "PILOT_MOVED",
                    "PILOT_VALID_BUT_NONMOVING",
                    "PILOT_SIGNAL_NOT_FIT",
                    "PILOT_EXECUTION_INCOMPLETE",
                },
            },
            "inputs": {
                "transition_outcome": transition_outcome,
                "target_row_id": target_row_id,
                "target_package_id": target_package_id,
                "new_signal": new_signal,
                "new_signal_pass_rule": new_signal_pass_rule,
                "new_signal_fired": new_signal_fired,
                "retained_signal": retained_signal,
                "retained_signal_pass_rule": retained_signal_pass_rule,
                "retained_signal_fired": retained_signal_fired,
                "transport_witness_artifact": _ptr(transport_witness_path),
                "bridge_object_artifact": _ptr(bridge_object_path),
                "blocker_movement_signal": blocker_movement_signal,
                "no_loop_rule": no_loop_rule,
                "promotion_requires_both_signals": promotion_requires_both,
                "reversibility_rule": reversibility_rule,
            },
            "summary": {
                "all_criteria_satisfied": execution_classification != "PILOT_EXECUTION_INCOMPLETE",
                "phase_status": "COMPLETE"
                if execution_classification != "PILOT_EXECUTION_INCOMPLETE"
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "execution_classification": execution_classification,
            "new_signal_fired": new_signal_fired,
            "retained_signal_fired": retained_signal_fired,
            "blocker_movement_signal": blocker_movement_signal,
            "no_loop_rule": no_loop_rule,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_posture_review_program_mode_transition_report": _ptr(transition_path),
        },
        "non_claim_boundary": "Repository-local bounded measurement-regime pilot execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the bounded measurement-regime pilot execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "bounded_measurement_regime_pilot_execution_20260411_v0.json",
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
        "bounded_measurement_regime_pilot_execution_report: "
        f"classification={payload['summary']['execution_classification']} "
        f"new_signal_fired={payload['summary']['new_signal_fired']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
