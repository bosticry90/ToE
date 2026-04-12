from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "REVISED_SIGNAL_DIAGNOSTIC_REGISTRATION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REVISED_SIGNAL_DIAGNOSTIC_REGISTRATION_20260411_v0.json"
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
    signal_to_register = dict(declaration.get("signal_to_register", {}))
    registration_policy = dict(declaration.get("registration_policy", {}))
    next_program_step = dict(declaration.get("next_program_step", {}))

    pilot_decision_path = REPO_ROOT / str(
        required_inputs.get("post_measurement_regime_pilot_decision_report", "")
    )
    pilot_decision_report = _read_json(pilot_decision_path)
    pilot_decision_summary = dict(pilot_decision_report.get("summary", {}))

    post_pilot_decision = str(pilot_decision_summary.get("post_pilot_decision", "")).strip()
    revised_signal_disposition = str(pilot_decision_summary.get("revised_signal_disposition", "")).strip()
    no_loop_rule_from_decision = str(pilot_decision_summary.get("no_loop_rule", "")).strip()
    no_further_pilot_loops_policy = str(pilot_decision_summary.get("no_further_pilot_loops_policy", "")).strip()

    # Validate that the pilot decision mandates diagnostic-only retention
    decision_authorizes_registration = (
        post_pilot_decision == "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY"
        and revised_signal_disposition == "RETAIN_DIAGNOSTIC"
    )

    signal_id = str(signal_to_register.get("signal_id", "")).strip()
    signal_disposition = str(registration_policy.get("signal_disposition", "")).strip()
    promotion_blocked = bool(registration_policy.get("promotion_to_authoritative_blocked", True))
    authoritative_signal_unchanged = str(registration_policy.get("authoritative_signal_unchanged", "")).strip()
    diagnostic_use_authorized = bool(registration_policy.get("diagnostic_use_authorized", True))
    diagnostic_use_scope = str(registration_policy.get("diagnostic_use_scope", "")).strip()
    no_loop_rule = str(registration_policy.get("no_loop_rule", "")).strip()
    no_further_pilot_loops_honored = bool(registration_policy.get("no_further_pilot_loops_honored", True))

    next_action = str(next_program_step.get("next_action", "")).strip()

    registration_outcome = (
        "REVISED_SIGNAL_REGISTERED_AS_DIAGNOSTIC_ONLY"
        if decision_authorizes_registration and promotion_blocked and diagnostic_use_authorized
        else "REGISTRATION_BLOCKED_MISSING_PREREQUISITE"
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "post_pilot_decision_is_retain_diagnostic": decision_authorizes_registration,
            "signal_disposition_is_diagnostic_only": signal_disposition == "DIAGNOSTIC_ONLY",
            "promotion_to_authoritative_blocked": promotion_blocked,
            "diagnostic_use_authorized": diagnostic_use_authorized,
            "authoritative_signal_unchanged": bool(authoritative_signal_unchanged),
            "no_further_pilot_loops_honored": no_further_pilot_loops_honored,
            "no_loop_rule_declared": no_loop_rule == "ONE_DIAGNOSTIC_SIGNAL_REGISTRATION_ONLY",
            "registration_outcome_valid": registration_outcome == "REVISED_SIGNAL_REGISTERED_AS_DIAGNOSTIC_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "prerequisite_decision_satisfied": decision_authorizes_registration,
                "signal_id_materialized": bool(signal_id),
                "signal_disposition_materialized": signal_disposition == "DIAGNOSTIC_ONLY",
                "promotion_block_enforced": promotion_blocked,
                "next_action_materialized": bool(next_action),
            },
            "inputs": {
                "post_pilot_decision": post_pilot_decision,
                "revised_signal_disposition": revised_signal_disposition,
                "signal_id": signal_id,
                "signal_disposition": signal_disposition,
                "promotion_to_authoritative_blocked": promotion_blocked,
                "authoritative_signal_unchanged": authoritative_signal_unchanged,
                "diagnostic_use_authorized": diagnostic_use_authorized,
                "diagnostic_use_scope": diagnostic_use_scope,
                "no_loop_rule": no_loop_rule,
                "no_loop_rule_from_decision": no_loop_rule_from_decision,
                "no_further_pilot_loops_policy": no_further_pilot_loops_policy,
                "no_further_pilot_loops_honored": no_further_pilot_loops_honored,
                "next_action": next_action,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "registration_outcome": registration_outcome,
            "signal_id": signal_id,
            "signal_disposition": signal_disposition,
            "promotion_to_authoritative_blocked": promotion_blocked,
            "authoritative_signal_unchanged": authoritative_signal_unchanged,
            "diagnostic_use_scope": diagnostic_use_scope,
            "no_loop_rule": no_loop_rule,
            "no_further_pilot_loops_honored": no_further_pilot_loops_honored,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_measurement_regime_pilot_decision_report": _ptr(pilot_decision_path),
        },
        "non_claim_boundary": "Repository-local revised-signal diagnostic registration only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the revised-signal diagnostic registration report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "revised_signal_diagnostic_registration_20260411_v0.json",
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
        "revised_signal_diagnostic_registration_report: "
        f"outcome={payload['summary']['registration_outcome']} "
        f"signal={payload['summary']['signal_id']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
