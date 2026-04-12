from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "BOUNDED_MEASUREMENT_REGIME_PILOT_RULING_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "BOUNDED_MEASUREMENT_REGIME_PILOT_RULING_20260411_v0.json"
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
    ruling_policy = dict(declaration.get("ruling_policy", {}))

    execution_path = REPO_ROOT / str(
        required_inputs.get("bounded_measurement_regime_pilot_execution_report", "")
    )
    execution_report = _read_json(execution_path)
    execution_summary = dict(execution_report.get("summary", {}))

    execution_classification = str(execution_summary.get("execution_classification", "")).strip()
    new_signal_fired = bool(execution_summary.get("new_signal_fired", False))
    retained_signal_fired = bool(execution_summary.get("retained_signal_fired", False))
    blocker_movement_signal = str(execution_summary.get("blocker_movement_signal", "")).strip()
    no_loop_rule = str(execution_summary.get("no_loop_rule", "")).strip()

    promotion_requires_both = bool(ruling_policy.get("promotion_requires_both_signals", True))

    moved_rule = str(ruling_policy.get("moved_rule", "")).strip()
    valid_but_nonmoving_rule = str(ruling_policy.get("valid_but_nonmoving_rule", "")).strip()
    not_fit_rule = str(ruling_policy.get("not_fit_rule", "")).strip()

    if execution_classification == "PILOT_MOVED":
        # Both signals must have fired for promotion-worthy movement
        if promotion_requires_both and new_signal_fired and retained_signal_fired:
            pilot_ruling = "REVISED_SIGNAL_REVEALED_MEANINGFUL_MOVEMENT"
            next_action = str(ruling_policy.get("next_action_if_moved", "")).strip() or (
                "PROMOTE_REVISED_MEASUREMENT_REGIME_AND_EXECUTE_NEXT_SEAM_TRANCHE"
            )
        else:
            # New signal fired but promotion requires both — demote to nonmoving
            pilot_ruling = "REVISED_SIGNAL_VALID_BUT_NONMOVING"
            next_action = str(ruling_policy.get("next_action_if_nonmoving", "")).strip() or (
                "ASSESS_PILOT_RESULT_AND_DECIDE_ROLLBACK_OR_HOLD"
            )
    elif execution_classification == "PILOT_VALID_BUT_NONMOVING":
        pilot_ruling = "REVISED_SIGNAL_VALID_BUT_NONMOVING"
        next_action = str(ruling_policy.get("next_action_if_nonmoving", "")).strip() or (
            "ASSESS_PILOT_RESULT_AND_DECIDE_ROLLBACK_OR_HOLD"
        )
    elif execution_classification == "PILOT_SIGNAL_NOT_FIT":
        pilot_ruling = "REVISED_SIGNAL_NOT_FIT_FOR_PROMOTION_USE"
        next_action = str(ruling_policy.get("next_action_if_not_fit", "")).strip() or (
            "ROLLBACK_REVISED_MEASUREMENT_REGIME_AND_HOLD"
        )
    else:
        pilot_ruling = "PILOT_RULING_INCOMPLETE"
        next_action = "RESTORE_PILOT_EXECUTION_PRECONDITIONS"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "execution_report_present": execution_path.exists(),
            "execution_classification_materialized": execution_classification
            in {
                "PILOT_MOVED",
                "PILOT_VALID_BUT_NONMOVING",
                "PILOT_SIGNAL_NOT_FIT",
            },
            "no_loop_rule_observed": no_loop_rule == "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
            "ruling_materialized": pilot_ruling != "PILOT_RULING_INCOMPLETE",
        },
        "objective_quality": {
            "criteria": {
                "moved_rule_supported": execution_classification == "PILOT_MOVED",
                "valid_but_nonmoving_rule_supported": execution_classification
                == "PILOT_VALID_BUT_NONMOVING"
                or (
                    execution_classification == "PILOT_MOVED"
                    and promotion_requires_both
                    and not retained_signal_fired
                ),
                "not_fit_rule_supported": execution_classification == "PILOT_SIGNAL_NOT_FIT",
                "ruling_materialized": pilot_ruling != "PILOT_RULING_INCOMPLETE",
            },
            "inputs": {
                "execution_classification": execution_classification,
                "new_signal_fired": new_signal_fired,
                "retained_signal_fired": retained_signal_fired,
                "blocker_movement_signal": blocker_movement_signal,
                "promotion_requires_both_signals": promotion_requires_both,
                "moved_rule": moved_rule,
                "valid_but_nonmoving_rule": valid_but_nonmoving_rule,
                "not_fit_rule": not_fit_rule,
                "no_loop_rule": no_loop_rule,
            },
            "summary": {
                "all_criteria_satisfied": pilot_ruling != "PILOT_RULING_INCOMPLETE",
                "phase_status": "COMPLETE"
                if pilot_ruling != "PILOT_RULING_INCOMPLETE"
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "pilot_ruling": pilot_ruling,
            "execution_classification": execution_classification,
            "new_signal_fired": new_signal_fired,
            "retained_signal_fired": retained_signal_fired,
            "no_loop_rule": no_loop_rule,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bounded_measurement_regime_pilot_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local bounded measurement-regime pilot ruling report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the bounded measurement-regime pilot ruling report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "bounded_measurement_regime_pilot_ruling_20260411_v0.json",
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
        "bounded_measurement_regime_pilot_ruling_report: "
        f"ruling={payload['summary']['pilot_ruling']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
